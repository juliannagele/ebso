(*   Copyright 2019 Julian Nagele and Maria A Schett

   Licensed under the Apache License, Version 2.0 (the "License");
   you may not use this file except in compliance with the License.
   You may obtain a copy of the License at

       http://www.apache.org/licenses/LICENSE-2.0

   Unless required by applicable law or agreed to in writing, software
   distributed under the License is distributed on an "AS IS" BASIS,
   WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
   See the License for the specific language governing permissions and
   limitations under the License.
*)
open Core
open Z3util

module PC = Program_counter
module SI = Stack_index

type t = {
  el : Z3.Expr.expr -> Z3.Expr.expr -> Z3.Expr.expr;
  decl : Z3.FuncDecl.func_decl;
  ctr_decl : Z3.FuncDecl.func_decl;
  ctr : Z3.Expr.expr -> Z3.Expr.expr;
}

let mk ea idx =
  let mk_vars_sorts vs = List.map vs ~f:(fun _ -> !Word.sort) in
  let vars_sorts = mk_vars_sorts (Enc_consts.forall_vars ea) in
  let sk = func_decl ("stack" ^ idx) (vars_sorts @ [PC.sort; !SI.sort]) !Word.sort in
  let c = func_decl ("sc" ^ idx) [PC.sort] !SI.sort in
  {
    (* stack(x0 ... x(sd-1), j, n) = nth word on stack after j instructions
       starting from a stack that contained words x0 ... x(sd-1) *)
    el = (fun j n -> sk <@@> (Enc_consts.forall_vars ea @ [j; n]));
    decl = sk;
    (* sc(j) = index of the next free slot on the stack after j instructions *)
    ctr_decl = c;
    ctr = (fun j -> c <@@> [j]);
  }

let init sk skd xs =
  let open Z3Ops in
  (* set stack counter to skd *)
  (sk.ctr PC.init == SI.enc skd)
  (* set inital words on stack *)
  && conj (List.mapi xs ~f:(fun i x -> sk.el PC.init (SI.enc i) == x))

let enc_equiv_at sks skt js jt =
  let open Z3Ops in
  let n = SI.const "n" in
  (* source and target stack counter are equal *)
  sks.ctr js == skt.ctr jt &&
  (* source and target stack are equal below the stack counter;
     note that it doesn't matter which stack counter is used, they are equal *)
  (forall n ((n < skt.ctr jt) ==> ((sks.el js n) == (skt.el jt n))))

(* get the top d elements of the stack *)
let enc_top_d sk j d =
  let open Z3Ops in
  let pos l = (sk.ctr j) - SI.enc (Int.succ l) in
  List.init d ~f:(fun l -> sk.el j (pos l))

let enc_push a sk j x =
  let open Z3Ops in
  (* the stack after the PUSH *)
  let sk' n = sk.el (j + one) n in
  (* the stack counter before the PUSH *)
  let sc = sk.ctr j in
  (* the new top word will be x *)
  sk' sc == Pusharg.enc a j x

(* the only effect of POP is to change the stack counter *)
let enc_pop _ _ = top

let enc_unaryop sk j op =
  let open Z3Ops in
  let sc = sk.ctr j and sc'= sk.ctr (j + one) in
  (sk.el (j + one) (sc' - SI.enc 1) == op (sk.el j (sc - SI.enc 1)))

let enc_binop sk j op =
  let open Z3Ops in
  let sc = sk.ctr j and sc'= sk.ctr (j + one) in
  (* the new top word is the result of applying op to the previous two *)
  (sk.el (j + one) (sc' - SI.enc 1) == op (sk.el j (sc - SI.enc 1)) (sk.el j (sc - SI.enc 2)))

let enc_ternaryop sk j op =
  let open Z3Ops in
  let sc = sk.ctr j and sc'= sk.ctr (j + one) in
  let w3 = sk.el j (sc - SI.enc 3)
  and w2 = sk.el j (sc - SI.enc 2)
  and w1 = sk.el j (sc - SI.enc 1) in
  sk.el (j + one) (sc' - SI.enc 1) == op w1 w2 w3

let enc_swap sk j idx =
  let sc_idx = SI.enc (idx + 1) in
  let open Z3Ops in
  let sc = sk.ctr j and sc'= sk.ctr (j + one) in
  (* the new top word is the 1+idx'th from the old stack *)
  (sk.el (j + one) (sc' - SI.enc 1) == sk.el j (sc - sc_idx)) &&
  (* the new 1+idx'th word is the top from the old stack*)
  (sk.el (j + one) (sc' - sc_idx) == sk.el j (sc - SI.enc 1)) &&
  (* the words between top and idx+1 are not touched *)
  conj (List.init (Int.pred idx) ~f:(fun i ->
      let sc_iidx = SI.enc (Int.(-) idx i) in
      (sk.el (j + one) (sc' - sc_iidx) == sk.el j (sc - sc_iidx))))

let enc_dup sk j idx =
  let sc_idx = SI.enc idx in
  let open Z3Ops in
  let sc = sk.ctr j and sc'= sk.ctr (j + one) in
  (* the new top word is the idx'th from the old stack *)
  (sk.el (j + one) (sc' - SI.enc 1) == sk.el j (sc - sc_idx)) &&
  (* all words down to idx are not touched *)
  conj (List.init idx ~f:(fun i ->
      let sc_iidx = SI.enc (Int.(-) idx i) in
      (sk.el (j + one) (sc - sc_iidx) == sk.el j (sc - sc_iidx))))

let pres is sk j =
  let open Z3Ops in
  let (d, _) = Instruction.delta_alpha is in
  let n = SI.const "n" in
  let sc = sk.ctr j in
  (* all words below d stay the same *)
  (forall n ((n < sc - SI.enc d) ==> (sk.el (j + one) n == sk.el j n)))

let enc_stack_ctr is sk j =
  let (d, a) = Instruction.delta_alpha is in let diff = (a - d) in
  let open Z3Ops in
  sk.ctr (j + one) == (sk.ctr j + SI.enc diff)
