(* Error codes. *)

Inductive error_code : Set := 
| NOT_DEFINED 
| FILE_NOT_FOUND 
| ACCESS_VIOLATION
| DISK_FULL_OR_ALLOCATION_EXCEEDED
| ILLEGAL_TFTP_OPERATION
| UNKNOWN_TRANSFER_ID
| FILE_ALREADY_EXISTS
| NO_SUCH_USER.

Definition err_code_to_nr (err : error_code) : N := 
  match err with 
  | NOT_DEFINED => 0
  | FILE_NOT_FOUND => 1
  | ACCESS_VIOLATION => 2
  | DISK_FULL_OR_ALLOCATION_EXCEEDED => 3
  | ILLEGAL_TFTP_OPERATION => 4
  | UNKNOWN_TRANSFER_ID => 5
  | FILE_ALREADY_EXISTS => 6
  | NO_SUCH_USER => 7
  end.

Definition nr_to_err_code (nr : N) : option error_code :=
  match nr with
  | N0 => Some NOT_DEFINED
  | Npos 1 => Some FILE_NOT_FOUND 
  | Npos 2 => Some ACCESS_VIOLATION
  | Npos 3 => Some DISK_FULL_OR_ALLOCATION_EXCEEDED
  | Npos 4 => Some ILLEGAL_TFTP_OPERATION
  | Npos 5 => Some UNKNOWN_TRANSFER_ID
  | Npos 6 => Some FILE_ALREADY_EXISTS
  | Npos 7 => Some NO_SUCH_USER
  | _ => None
  end.

Theorem err_code_nr_ident : forall err, Some err = nr_to_err_code (err_code_to_nr err).
Proof.
intros.
destruct err; simpl; auto.
Qed.

Definition err_code_to_string (err : error_code) : string :=
  word_no_to_string (err_code_to_nr err).

Definition string_to_err_code (s : string) : option error_code := 
  string_to_word_no s >>= nr_to_err_code.

Theorem err_code_string_ident : forall err, Some err = string_to_err_code (err_code_to_string err).
Proof.
intros.
case err;
unfold err_code_to_string;
simpl;
unfold word_no_to_string;
simpl;
unfold string_to_err_code;
simpl;
auto.
Qed.