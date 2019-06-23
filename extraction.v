Require client.

Require Import ExtrOcamlBasic.
Require Import ExtrOcamlString.

Extraction Blacklist String Int List Nat.

Separate Extraction
         BinNat BinNums BinInt BinPos (* to jest potrzebne do camlcoq *)
         client.
