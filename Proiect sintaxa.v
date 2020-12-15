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
Notation "A \a B" := (adiv A B)(at level 48, left associativity).
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
Notation "'FOR' A '~~' B '~~' C '{' S '}'" := (for_ A B C S) (at level 90).
Notation "'IF_' B 'THEN_' S" := (ifthen B S) (at level 90).
Notation "'IF' B 'THEN' S1 'ELSE' S2" :=(ifthenelse B S1 S2)(at level 50).
Notation "'DO_WHILE' '<<<<' S '>>>>' B" :=(do_while S B)(at level 89).
Notation "'WHILE' B '{' S '}'" := (while B S)(at level 89).

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
  IStr "ceva" ::= "mai" ;;
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
    CALL ? "do_something" ? ;;
    IF_ ( "a" <b "d" )
    THEN_ ( "array" :a= Carray(start_array 3) 5) 
  }
.

Print Program.

Inductive Result :=
  | err_undecl : Result
  | err_assign : Result
  | default : Result
  | res_nat : Number_Value -> Result
  | res_bool : Boolean_Value -> Result
  | res_string : String_Value -> Result
  | res_array : Array_Value -> Result
  | code : Stmt -> Result. (* The functions' names are mapped to the code inside the function *)



Inductive Mem :=
  | mem_default : Mem
  | offset : nat -> Mem. (* offset which indicates the current number of memory zones *)

Scheme Equality for Mem.

(* Environment *)
Definition Env := string -> Mem.

(* Memory Layer *)
Definition MemLayer := Mem -> Result.

(* Stack *)
Definition Stack := list Env.

(* Configuration *)
Inductive Config :=
  (* nat: last memory zone
     Env: environment
     MemLayer: memory layer
     Stack: stack 
  *)
  | config : nat -> Env -> MemLayer -> Stack -> Config.

(* Function for updating the environment *)
Definition update_env (env: Env) (x: string) (n: Mem) : Env :=
  fun y =>
      (* If the variable has assigned a default memory zone, 
         then it will be updated with the current memory offset *)
      if (andb (string_beq x y ) (Mem_beq (env y) mem_default))
      then
        n
      else
        (env y).

Definition env : Env := fun x => mem_default.

(* Initially each variable is assigned to a default memory zone *)
Compute (env "z"). (* The variable is not yet declared *)

(* Example of updating the environment, based on a specific memory offset *)
Definition env2  := (update_env env "x" (offset 9)).

Compute env2 "x".

Definition check_eq_over_types (t1 : Result) (t2 : Result) : bool :=
  match t1 with
  | err_assign => match t2 with 
                    | err_assign => true
                    | _ => false
                     end
  | err_undecl => match t2 with
                    | err_undecl => true
                    | _ => false
                     end
  | default => match t2 with
                 | default => true
                 | _ => false
               end
  | res_bool _x => match t2 with
                     | res_bool _y => true
                     | _ => false
                   end
  | res_nat _x => match t2 with
                     | res_nat _y => true
                     | _ => false
                  end
  | res_string _x => match t2 with
                       | res_string _y => true
                       | _ => false
                      end
  | res_array _x => match t2 with
                       | res_array _y => true
                       | _ => false
                    end
  | code _x => match t2 with 
                 | code _y => true
                 | _ => false
               end
end.
(*

(* Function for updating the memory layer *)
Definition update_mem (mem : MemLayer) (env : Env) (x : string) (type : Mem) (v : Result) : MemLayer :=
  fun y =>
    (* To be implemented based on the functionalities of your own language
       This implementation should be similar to the "update" function from "Week_7.v" *)



(* Each variable/function name is initially mapped to undeclared *)
Definition mem : MemLayer := fun x => err_undecl.

(* Pay attention!!! In order to be able to monitor the state of the entire program, you need to
   implement a function "update_conf", which updates the 
   entire configuration (environment, memory layout and stack).  
   config : nat -> Env -> MemLayer -> Stack -> Config (the first value represents the last memory zone, 
   and you will need to find a way to increment it each time a new variable/function is declared)
*)

(* Functions / global/local variables *)
(*
  - Restructurare program: declaratii de variabile / declaratii de functii
  - In Stmt trebuie adaugat si apelul de functii (care este sintaxa?)
  - Liste de argumente pentru functii: List type.
  - Atentie la sintaxa!!!
  - Referinte/pointeri: lucrul cu zona de memorie
  - Vectori: de asigurat ca se pot pastra n zone de memorie in functie de dimensiunea vectorului.
*)
