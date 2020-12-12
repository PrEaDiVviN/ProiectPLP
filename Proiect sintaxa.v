(* Librariile necesare pentru string-uri *)
Require Import Strings.String.
Local Open Scope string_scope.
Local Open Scope list_scope.
Scheme Equality for string. (* Creaza functia de egalitate pe string-uri automat *)

(* Librarii necesare pentru numere intregi *)
Require Import Coq.ZArith.ZArith.
Open Scope Z_scope.  


Inductive Number_Value :=
| error_number : Number_Value
| Cnum : Z -> Number_Value. 

Inductive Boolean_Value :=
| error_bool : Boolean_Value
| Cbool : bool -> Boolean_Value.

Inductive String_Value :=
| error_string : String_Value
| empty_string : String_Value
| Cstring : string -> String_Value.

Inductive Array_Value :=
| error_array : Array_Value
| empty_array : Array_Value
| start_array : Z -> Array_Value
| Carray : Array_Value -> Z -> Array_Value.

Coercion Cnum: Z >-> Number_Value.
Coercion Cbool: bool >-> Boolean_Value.
Coercion Cstring: string >-> String_Value.

Definition example : Array_Value := start_array 5.
Compute example.

Definition example2 := Carray example 5.
Compute example2.

Definition example3 := Carray example2 100.
Compute example3.


