(* Librariile necesare pentru string-uri *)
Require Import Strings.String.
Local Open Scope string_scope.
Local Open Scope list_scope.
Scheme Equality for string. (* Creaza functia de egalitate pe string-uri automat *)

(* Librarii necesare pentru numere intregi *)
Require Import Coq.ZArith.ZArith.
Open Scope Z_scope.  

(* Liste *)
Local Open Scope list_scope.


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

(* Expresii aritmetice *)
Inductive AExp :=
| avar: string -> AExp 
| acon: Number_Value -> AExp
| aplus: AExp -> AExp -> AExp
| asub: AExp -> AExp -> AExp
| amul: AExp -> AExp -> AExp 
| adiv: AExp -> AExp -> AExp 
| amod: AExp -> AExp -> AExp.



(* Notatiile pentru operatiile aritmetice *)
Notation "A +a B" := (aplus A B)(at level 50, left associativity).
Notation "A -a B" := (asub A B)(at level 50, left associativity).
Notation "A *a B" := (amul A B)(at level 48, left associativity).
Notation "A /a B" := (adiv A B)(at level 48, left associativity).
Notation "A %a B" := (amod A B)(at level 45, left associativity).

Coercion acon: Number_Value >-> AExp.
Coercion avar: string >-> AExp.

Compute ((Cnum 5) -a "string").

(* Expresii boolene *)
Inductive BExp :=
| bvar : string -> BExp
| bcon: Boolean_Value -> BExp
| blt : AExp -> AExp -> BExp
| bnot : BExp -> BExp
| band : BExp -> BExp -> BExp
| bor : BExp -> BExp -> BExp.



(* Expresii string-uri *)
Inductive STExp :=
| svar : string -> STExp
| svar : String_Value -> STExp
| sconcat : STExp ->STExp -> STExp
| smul : STExp -> Z -> STExp.

(* Expresii vectori *)
Inductive VExp :=
| vvar : Array_Value -> VExp
| vadd : VExp -> Z -> VExp
| vmull : VExp -> Z -> VExp
| vmin : VExp -> Z -> VExp
| vsuply : VExp -> Z -> VExp
| vconcat : VExp -> VExp -> VExp.

Inductive Cases :=
| first : string -> Cases
| next : string -> Cases -> Cases.

(* Sectiunea pentru statement-uri *)
Inductive Stmt :=
| number_decl: string -> AExp -> Stmt  
| bool_decl: string -> BExp -> Stmt  
| string_decl: string -> STExp -> Stmt
| array_decl: string -> VExp -> Stmt
| number_assign : string -> AExp -> Stmt
| bool_assign : string -> BExp -> Stmt
| string_assign : string -> STExp -> Stmt
| vector_assign : string -> STExp -> Stmt
| sequence : Stmt -> Stmt -> Stmt
| while : BExp -> Stmt -> Stmt
| do_while: Stmt -> BExp -> Stmt
| for_ : Stmt -> BExp -> Stmt -> Stmt -> Stmt
| break : Stmt
| continue : Stmt
| ifthenelse : BExp -> Stmt -> Stmt -> Stmt
| ifthen : BExp -> Stmt -> Stmt
| function : string -> Stmt -> Stmt
| function_call : string -> Stmt
| switch_case : Cases -> Stmt.



(* Notations used for boolean operations *)
Notation "A <' B" := (blt A B) (at level 70).
Notation "!' A" := (bnot A)(at level 51, left associativity).
Notation "A &&' B" := (band A B)(at level 52, left associativity).
Notation "A ||' B" := (bor A B)(at level 53, left associativity).

(* Notations for Statements *)
Notation "X :n= A" := (nat_assign X A)(at level 90).
Notation "X :b= A" := (bool_assign X A)(at level 90).
Notation "'iNat' X ::= A" := (nat_decl X A)(at level 90).
Notation "'iBool' X ::= A" := (bool_decl X A)(at level 90).
Notation "S1 ;; S2" := (sequence S1 S2) (at level 93, right associativity).
Notation "'fors' ( A ~ B ~ C ) { S }" := (A ;; while B ( S ;; C )) (at level 97).
