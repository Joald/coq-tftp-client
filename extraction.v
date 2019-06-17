Require Coq_uniq.

Require Import ExtrOcamlBasic.
Require Import ExtrOcamlString.

Extraction Blacklist String Int List Nat.

(* tak można wstawiać ocamlowy kod do aksjomatów *)
Extract Constant Coq_uniq.newline => "'\n'".

Separate Extraction
         BinNat BinNums BinInt BinPos (* to jest potrzebne do camlcoq *)
         Coq_uniq.
