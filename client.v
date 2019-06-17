Require Import ZArith.
Require Import String.

Require Import packet.

Inductive mode : Set := Read | Write.

Record init_state : Set := mkState {
    transfer_mode : mode;
    filename : string;
    port: positive;
    last_packet : option packet;
    timeout_count : N;
}.

Definition coq_process_state () := .
