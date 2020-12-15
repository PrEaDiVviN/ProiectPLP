(* Librariile necesare pentru string-uri *)
Require Import Strings.String.
Local Open Scope string_scope.
Local Open Scope list_scope.
Scheme Equality for string. (* Creaza functia de egalitate pe string-uri automat *)

(* Librarii necesare pentru numere intregi *)
Require Import Coq.ZArith.ZArith.
Open Scope Z_scope.  

(* Liste si notatiile pentru ele *)
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
| name : string -> Array_Value
| error_array : Array_Value
| empty_array : Array_Value
| start_array : Z -> Array_Value
| Carray : Array_Value -> Z -> Array_Value.

Compute Carray (Carray (start_array 3) 9) 5.
 
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

Compute ((Cnum 5) -a "string"). (* EXEMPLU AExp *)

(* Expresii boolene *)
Inductive BExp :=
| bvar : string -> BExp
| bcon: Boolean_Value -> BExp
| begal: AExp -> AExp -> BExp
| blt : AExp -> AExp -> BExp
| bnot : BExp -> BExp
| band : BExp -> BExp -> BExp
| bor : BExp -> BExp -> BExp.

(* Notations used for boolean operations *)
Notation "A <b B" := (blt A B) (at level 50).
Notation "A ==b B" := (begal A B) (at level 50).
Notation "!b A" := (bnot A)(at level 51, left associativity).
Notation "A &&b B" := (band A B)(at level 52, left associativity).
Notation "A ||b B" := (bor A B)(at level 53, left associativity).

Coercion bcon: Boolean_Value >-> BExp.
Coercion bvar: string >-> BExp.

Compute !b (("a" +a 5) ==b 7). (* EXEMPLU BExp *)

(* Expresii string-uri *)
Inductive STExp :=
| scon : String_Value -> STExp
| sconcat : STExp ->STExp -> STExp
| smul : STExp -> Z -> STExp.

Notation "A +Us+ B" := (sconcat A B)(at level 70).
Notation "A *** B" := (smul A B)(at level 70).

Coercion scon: String_Value >-> STExp.

Compute ("ceva" *** 3) +Us+ "BUN".

(* Expresii vectori *)
Inductive VExp :=
| vvar : Array_Value -> VExp
| vadd : VExp -> Z -> VExp
| vmull : VExp -> Z -> VExp
| vmin : VExp -> Z -> VExp
| vsuply : VExp -> Z -> VExp
| vconcat : VExp -> VExp -> VExp.

Coercion vvar: Array_Value >-> VExp.

Notation "A +v B" := (vadd A B)(at level 70).
Notation "A *v B" := (vmull A B)(at level 70).
Notation "A -v B" := (vmin A B)(at level 70).
Notation "A +Uv B" := (vsuply A B)(at level 70).
Notation "A +Uv+ B" := (vconcat A B)(at level 70).

Compute ((Carray (Carray (start_array 3) 9) 5) +Uv+ (start_array 15)) -v 15.



(* Sectiunea pentru statement-uri *)
Inductive Stmt :=
| number_decl: string -> AExp -> Stmt  
| bool_decl: string -> BExp -> Stmt  
| string_decl: string -> STExp -> Stmt
| array_decl: string -> VExp -> Stmt
| number_assign : string -> AExp -> Stmt
| bool_assign : string -> BExp -> Stmt
| string_assign : string -> STExp -> Stmt
| array_assign : string -> STExp -> Stmt
| sequence : Stmt -> Stmt -> Stmt
| while : BExp -> Stmt -> Stmt
| do_while: Stmt -> BExp -> Stmt
| for_ : Stmt -> BExp -> Stmt -> Stmt -> Stmt
| break : Stmt
| continue : Stmt
| ifthenelse : BExp -> Stmt -> Stmt -> Stmt
| ifthen : BExp -> Stmt -> Stmt
| function_decl : string -> list Stmt -> Stmt -> Stmt
| function_call : string -> Stmt
| case : AExp -> Stmt -> Stmt
| switch_case : AExp -> list Stmt  -> Stmt.


(* Notations for Statements *)
Notation "X :n= A" := (number_assign X A)(at level 90).
Notation "X :b= A" := (bool_assign X A)(at level 90).
Notation "X :s= A" := (string_decl X A)(at level 90).
Notation "X :a= A" := (array_decl X A)(at level 90).
Notation "'INat' X ::= A" := (number_decl X A)(at level 90).
Notation "'IBool' X ::= A" := (bool_decl X A)(at level 90).
Notation "'IArr' X ::= A" := (array_decl X A)(at level 90).
Notation "'IStr' X ::= A" := (string_decl X A)(at level 90).
Notation "S1 ;; S2" := (sequence S1 S2) (at level 93, right associativity).
Notation "'FOR' '$' A '~' B '~' C '$' '{' S '}'" := (for_ A B C S) (at level 90).
Notation "'IF B 'THEN' S" := (ifthen B S) (at level 90).
Notation "'IF' B 'THEN' S1 'ELSE' S2" :=(ifthenelse B S1 S2)(at level 50).
Notation "'DO_WHILE' '<<<<' S '>>>>' B" :=(do_while S B)(at level 89).

Notation "'CALL' ? S ?" := (function_call S)(at level 90).
Notation "'function' N '&' L '&' '{' S '}'" := (function_decl N L S) (at level 91).


Module ListNotations.
Notation "[ ]" := nil. 
Notation "[ x ; .. ; y ]" := (cons x .. (cons y nil) ..).

Notation "'CASE' '@' N '@'  '#' S '#'" := (case N S) (at level 90).
Notation "'SWITCH' '(' A ')' '{' B '}'" := (switch_case A B)(at level 90).


Definition Program :=
  "b" :b= bcon (Cbool true) ;;
  "a" :n= 15 -a "b" ;;
  "string" :s= "text" +Us+ " ajutator" ;;
  "array" :a= Carray (Carray (start_array 3) 9) 5 ;;
  INat "a"  ::= 13 ;;
  IBool "b" ::= ("a" ==b 0) ;;
  IArr "array" ::= name "array" +Uv+ name "array"  ;;
  function "do_something"  & [ INat "c" ::= 0 ] &  { "b" :b= bcon (Cbool false) } ;;
  function "main" & [] &
  {
    IF ( "c" ==b 15 )
    THEN ( "c" :n= "c" +a 1 )
    ELSE
        ( "b" :b= bcon (Cbool false ) ) ;;
    SWITCH ( "c" ) 
        { [ (CASE @ 5 @ # INat "a" ::= 13 #) ; 
            (CASE @ 10 @ # INat "a" ::= 15 #) 
          ] 
        } ;; 
    DO_WHILE <<<< (break ;; continue) >>>> ("a" ==b 3) ;;
    CALL ? "do_something" ? 
  }
.

Print Program.
