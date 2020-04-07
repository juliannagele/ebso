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
open Z3util

type t = Z.t [@@deriving eq, compare]

let show = Z.to_string

let pp fmt n = Format.fprintf fmt "%s" (show n)

let sort = int_sort

let const = intconst

let enc = num

let dec = Z3.Arithmetic.Integer.get_big_int

let init = enc Z.zero

let of_int = Z.of_int

let to_int = Z.to_int
