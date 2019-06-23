Require Import ZArith.

Require Import String.
Require Import Ascii.

Open Scope char_scope.

AddPath "/Users/joald/wwk/client" as.

Load opcode.

Load errcode.

(* Packets. *)

Inductive mode : Set := Read | Write.

Local Open Scope N_scope.

Inductive packet : Set := 
| p_RRQ : string -> packet                  (* Filename *)
| p_WRQ : string -> packet                  (* Filename *)
| p_DATA : N -> string -> packet            (* Block #, Data *)
| p_ACK : N -> packet                       (* Block # *)
| p_ERROR : error_code -> string -> packet. (* ErrorCode, ErrMsg *)


Definition init_packet (m : mode) (in_filename : string) (out_filename : string) : packet := 
  match m with
  | Read => p_RRQ in_filename
  | Write => p_WRQ out_filename
  end.

Theorem init_packet_read_rrq : forall s_in s_out m, m = Read -> init_packet m s_in s_out = p_RRQ s_in.
Proof.
intros.
unfold init_packet.
rewrite H.
auto.
Qed.

Theorem init_packet_write_wrq : forall s_in s_out m, m = Write -> init_packet m s_in s_out = p_WRQ s_out.
Proof.
intros.
unfold init_packet.
rewrite H.
auto.
Qed.

Definition serialize_packet (p : packet) : string := 
  match p with
  | p_RRQ filename => opcode_to_string RRQ ++ null_terminate filename ++ null_terminate "octet"
  | p_WRQ filename => opcode_to_string WRQ ++ null_terminate filename ++ null_terminate "octet"
  | p_DATA block_no data => opcode_to_string DATA ++ word_no_to_string block_no ++ data
  | p_ACK block_no => opcode_to_string ACK ++ word_no_to_string block_no
  | p_ERROR err_code err_msg => opcode_to_string ERROR ++ err_code_to_string err_code ++ null_terminate err_msg
  end.

Definition deserialize_packet (s : string) : option packet.
Proof.
  refine (
  match s with
  | String zero (String x rest) => 
    match ascii_to_opcode x with
    | Some RRQ => None (* The client will never need to deserialize requests. *)
    | Some WRQ => None
    | Some DATA => 
      match rest with
      | String c1 (String c2 rest2) => 
        let s := two_ascii_to_string c1 c2 in _
      | _ => None
      end
    | Some ACK => 
      match rest with
      | String c1 (String c2 EmptyString) => 
        let s := two_ascii_to_string c1 c2 in _
      | _ => None
      end
    | Some ERROR => 
      match rest with
      | String c1 (String c2 rest2) => 
        let s := two_ascii_to_string c1 c2 in _
      | _ => None
      end
    | None => None
    end
  | _ => None
  end).
(* DATA *)
* refine (
    match string_to_word_no s with
    | Some n => Some (p_DATA n rest2)
    | None => None
    end
  ).
(* ACK *)
* refine (
    match string_to_word_no s with
    | Some n => Some (p_ACK n)
    | None => None
    end
  ).
(* ERROR *)
* refine (
    match string_to_word_no s with
    | Some n => _
    | None => None
    end
  ).
  refine (
    match nr_to_err_code n with
    | Some e => Some (p_ERROR e (remove_last rest2))
    | None => None
    end
  ).
Defined.

Lemma some_eq : forall A : Type, forall x y : A, x = y -> Some x = Some y.
Proof.
magics.
inversion H.
auto.
Qed.

Theorem rrq_serial_ident : forall s, deserialize_packet (serialize_packet (p_RRQ s)) = None.
Proof.
magics.
Qed.

Theorem wrq_serial_ident : forall s, deserialize_packet (serialize_packet (p_WRQ s)) = None.
Proof.
magics.
Qed.

Theorem data_serial_ident : 
  forall x x2 : N,
  forall s s2 : string, 
  forall H : x < two_bytes_range_size,
  forall H2 : x2 < two_bytes_range_size,
  match deserialize_packet (serialize_packet (p_DATA x s)) with 
  | Some (p_DATA x2 s2) => x = x2 /\ s = s2
  | Some _ => False
  | None => True
  end.
Proof with magics.
magic.
unfold byte_range_size.
rewrite (N_ascii_embedding (x / 256)).
* magic.
  rewrite (N_ascii_embedding (x mod 256)).
  + rewrite (N.mul_comm (x / 256) 256).
    rewrite <- (N.div_mod x 256)...
  + remember (N.mod_bound_pos x 256) as B.
    apply B.
    - elim x...
    - magics.
* magic.
  unfold two_bytes_range_size in H.

  cut (256 * x / 256 < 256 * 256).
  { magic.
    rewrite (N.mul_lt_mono_pos_r 256 (x / 256) 256).
    + assert (256 * (x / 256) <= 256 * x / 256).
      { rewrite (N.mul_comm 256 x).
        rewrite (N.div_mul x 256).
        rewrite (N.mul_div_le x 256)...
        easy. } 
    magics. 
    + magic. }
  rewrite (N.mul_comm 256 x).
  rewrite (N.div_mul x 256)...
Qed.

Theorem ack_serial_ident : 
  forall x x2 : N,
  forall s s2 : string, 
  forall H : x < two_bytes_range_size,
  forall H2 : x2 < two_bytes_range_size,
  match deserialize_packet (serialize_packet (p_ACK x)) with 
  | Some (p_ACK x2) => x = x2
  | Some _ => False
  | None => True
  end.
Proof with magics.
magic.
unfold byte_range_size.
rewrite (N_ascii_embedding (x / 256)).
* rewrite (N_ascii_embedding (x mod 256)).
  + rewrite (N.mul_comm (x / 256) 256).
    rewrite <- (N.div_mod x 256)...
  + apply (N.mod_bound_pos x 256).
    - elim x...
    - magics.
* magic.
  unfold two_bytes_range_size in H.

  cut (256 * x / 256 < 256 * 256).
  { magic.
    rewrite (N.mul_lt_mono_pos_r 256 (x / 256) 256).
    + assert (256 * (x / 256) <= 256 * x / 256).
      { rewrite (N.mul_comm 256 x).
        rewrite (N.div_mul x 256).
        rewrite (N.mul_div_le x 256)...
        easy. } 
      magics. 
    + magic. }
  rewrite (N.mul_comm 256 x).
  rewrite (N.div_mul x 256)...
Qed.

Theorem error_serial_ident : forall err s, deserialize_packet (serialize_packet (p_ERROR err s)) = Some (p_ERROR err s).
Proof with magics.
destruct err; magic; rewrite (null_determination s)...
Qed.

Theorem deserialized_num_less_than_two_byte_size : forall pac num data,
  deserialize_packet pac = Some (p_DATA num data) ->
  num < two_bytes_range_size.
Proof with magic.
intros.
unfold deserialize_packet in H.
destruct pac...
destruct pac...
destruct (ascii_to_opcode a0)...
destruct p...
* destruct pac...
  destruct pac...
  case_eq (string_to_word_no (two_ascii_to_string a1 a2)).
  + intros.
    assert (n < two_bytes_range_size).
    { apply (string_to_word_no_in_range (two_ascii_to_string a1 a2) n).
      assumption. }
    rewrite H0 in H.
    inversion H.
    rewrite H3 in H1.
    assumption.
  + magics.
* destruct pac...
  destruct pac...
  destruct pac...
* destruct pac...
  destruct pac...
  case_eq (string_to_word_no (two_ascii_to_string a1 a2)).
  + intros.
    assert (n < two_bytes_range_size).
    { apply (string_to_word_no_in_range (two_ascii_to_string a1 a2) n).
      assumption. }
    rewrite H0 in H.
    inversion H.
    destruct (nr_to_err_code n).
    - magics.
    - magics.
  + magics.
Qed.

Theorem deserialized_num_less_than_two_byte_size_but_its_ack : forall pac num,
  deserialize_packet pac = Some (p_ACK num) ->
  num < two_bytes_range_size.
Proof with magic.
intros.
unfold deserialize_packet in H.
destruct pac...
destruct pac...
destruct (ascii_to_opcode a0)...
destruct p...
* destruct pac...
  destruct pac...
* destruct pac...
  destruct pac...
  destruct pac...
  case_eq (string_to_word_no (two_ascii_to_string a1 a2)).
  + intros.
    assert (n < two_bytes_range_size).
    { apply (string_to_word_no_in_range (two_ascii_to_string a1 a2) n).
      assumption. }
    rewrite H0 in H.
    inversion H.
    rewrite H3 in H1.
    assumption.
  + magics.
* destruct pac...
  destruct pac...
  case_eq (string_to_word_no (two_ascii_to_string a1 a2)).
  + intros.
    assert (n < two_bytes_range_size).
    { apply (string_to_word_no_in_range (two_ascii_to_string a1 a2) n).
      assumption. }
    rewrite H0 in H.
    inversion H.
    destruct (nr_to_err_code n).
    - magics.
    - magics.
  + magics.
Qed.