Require Import List.
Import ListNotations.

Require Import Ascii.
Require Import String.
Open Scope string_scope.

Require Import ExtrOcamlBasic.
Require Import ExtrOcamlString.

(** < Core imports **)
From Verbatim Require Import state. (* LABEL lives here, maybe it shouldn't. *)
From Verbatim Require Import Utils.asciiSigma.
From Verbatim Require Import concrete_lexer.
From Verbatim Require Import _Utils.Lexer.
(** /> **)

(** Label type defined here **)
Module Export LABELS <: LABEL.

  Inductive Label' : Type :=
  | LEFT_PAREN
  | RIGHT_PAREN
  | INT
  | NAME
  | PLUS_OP
  | MINUS_OP
  | TIMES_OP
  | DIVIDE_OP
  | DEFUN
  | IF_OP
  | WS.

  Definition Label : Type := Label'.
  Definition defLabel : Label := WS.
  Lemma Label_eq_dec : forall (l l' : Label), {l = l'} + {l <> l'}.
  Proof. decide equality. Qed.

End LABELS.

(** Here is where the lexer is compiled **)
(* ALPHABET is the SIGMA object from asciiSigma *)
Module Export LXR := LexerFn ALPHABET LABELS.
(* Loads in regex library from _Utils.Lexer; Object R comes from LXR *)
Module Import PBR := prebuilt_regexes R.


(** White Space **)
(* [ \t\n\r] *)
(* ws_carr_re includes \r; ws_re does not *)
Definition ru_ws : Rule := (WS, ws_carr_re).


(** Numbers **)
Definition int_re := nat_re.

Definition ru_int := (INT, int_re).

(** Strings **)
Definition name_re := Plus (IterUnion [AZ_re; az_re]).
Definition run_name := (NAME, name_re).

(** Keywords **)
Definition ru_if := (IF_OP, stringApp "if").
Definition ru_defun := (DEFUN, stringApp "defun").

(** operators **)
Definition ru_plus := (PLUS_OP, stringApp "+").
Definition ru_minus := (MINUS_OP, stringApp "-").
Definition ru_timea := (TIMES_OP, stringApp "*").
Definition ru_divide := (DIVIDE_OP, stringApp "/").


(** brack, brace, colon, comma **)
Definition ru_lparen := (LEFT_PAREN, stringApp "(").
Definition ru_rparen := (RIGHT_PAREN, stringApp ")").


(** Compile rules and extract **)
Definition rus : list Rule :=
  [ru_ws;ru_int;ru_if;ru_defun;ru_plus;
  ru_minus;ru_timea;ru_divide;ru_lparen;ru_rparen;run_name].

Definition show_label (l : Label) : string :=
  match l with
  | LEFT_PAREN => "LEFT_PAREN"
  | RIGHT_PAREN => "RIGHT_PAREN"
  | INT => "INT"
  | NAME => "NAME"
  | PLUS_OP => "PLUS_OP"
  | MINUS_OP => "MINUUS_OP"
  | TIMES_OP => "TIMES_OP"
  | DIVIDE_OP => "DIVIDE_OP"
  | DEFUN => "DEFUN"
  | IF_OP => "IF"
  | WS => "ws"
  end.

Definition show_token (t : Token) : string :=
  match t with
  | (l, s) => show_label l ++ " | " ++ string_of_list_ascii s
  end.

Set Warnings "-extraction-opaque-accessed,-extraction".
Compute (extract_path "BasicLisp" Literal).
Extraction "Examples/BasicLisp/Evaluation/Literal/instance.ml" lex rus show_token.


