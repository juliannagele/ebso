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

let size = ref 3

let sort = ref (bv_sort !size)

let set_wsz n = size := n; sort := bv_sort !size

let enc_int n = Z3.Expr.mk_numeral_int !ctxt n !sort

let enc_string n = Z3.Expr.mk_numeral_string !ctxt n !sort

let const s = Z3.Expr.mk_const_s !ctxt s !sort
