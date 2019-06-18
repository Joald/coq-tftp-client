Require Import ZArith.

Require Import String.
Require Import Ascii.

Open Scope char_scope.


Unset Elimination Schemes.

AddPath "/Users/joald/wwk/client" as.

Load maybe.

Load aux.

Load opcode.

Load errcode.

(* Packets. *)

Inductive mode : Set := Read | Write.

Local Open Scope N_scope.

Inductive packet : Set := 
| p_RRQ : string -> packet                  (* Filename *)
| p_WRQ : string -> packet                  (* Filename *)
| p_DATA : forall (x : N), x < two_bytes_range_size -> string -> packet     (* Block #, Data *)
| p_ACK : forall (x : N), x < two_bytes_range_size -> packet                (* Block # *)
| p_ERROR : error_code -> string -> packet. (* ErrorCode, ErrMsg *)


Definition init_packet (m : mode) (filename : string) : packet := 
  match m with
  | Read => p_RRQ filename
  | Write => p_WRQ filename
  end.

Theorem init_packet_read_rrq : forall s : string, forall m : mode, m = Read -> init_packet m s = p_RRQ s.
Proof.
intros.
unfold init_packet.
rewrite H.
auto.
Qed.

Theorem init_packet_write_wrq : forall s : string, forall m : mode, m = Write -> init_packet m s = p_WRQ s.
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
  | p_DATA block_no _ data => opcode_to_string DATA ++ word_no_to_string block_no ++ data
  | p_ACK block_no _ => opcode_to_string ACK ++ word_no_to_string block_no
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
* remember (string_to_word_no s) as X.
  destruct X.
  + refine (Some (p_DATA n (string_to_word_no_in_range s n _) rest2)).
    auto.
  + exact None.
(* ACK *)
* remember (string_to_word_no s) as X.
  destruct X.
  + refine (Some (p_ACK n (string_to_word_no_in_range s n _))).
    auto.
  + exact None.
(* ERROR *)
* remember (string_to_word_no s) as X.
  destruct X.
  + remember (nr_to_err_code n) as opt.
    destruct opt.
    - refine (Some (p_ERROR e rest2)).
    - exact None.
  + exact None.
Defined.

Lemma some_eq : forall A : Type, forall x y : A, x = y -> Some x = Some y.
Proof.
magics.
inversion H.
auto.
Qed.
(*
Import EqNotations.
Lemma args_ok : forall x1 x2 : N, forall H : x1 = x2, forall v, forall y1 : x1 < v, forall y2 : x2 < v, rew H in (y1 = y2).

Lemma data_ok : forall x1 x2 z1 z2, forall H : x1 = x2, z1 = z2 -> p_DATA x1 y z1 = p_DATA x2 y z2.
*)
(*
Theorem packet_string_ident : forall p, deserialize_packet (serialize_packet p) = Some p \/ deserialize_packet (serialize_packet p) = None.
Proof with magics.
magics.
destruct p...
* left.
  apply (some_eq packet _ _).
  assert ((N_of_ascii (ascii_of_N (x / byte_range_size)) *
   byte_range_size +
   N_of_ascii (ascii_of_N (x mod byte_range_size))) = x).
  { rewrite (N_ascii_embedding (x / byte_range_size)).
    + rewrite (N_ascii_embedding (x mod byte_range_size)); unfold byte_range_size.
      - admit.
      - unfold two_bytes_range_size in l.
        remember (N.mod_bound_pos x 256) as B.
        apply B.
        -- elim x...
        -- magic.
    + unfold byte_range_size.
      unfold two_bytes_range_size in l.
      admit. }
  rewrite <- H.
  unfold byte_range_size...
  unfold string_to_word_no_in_range.
      

rewrite (N.mul_comm (x / 256) 256)...
  assert (forall x1 x2 y z1 z2, x1 = x2 -> z1 = z2 -> p_DATA x1 y z1 = p_DATA x2 y z2).
  Check N_ascii_embedding.
  unfold byte_range_size.
  rewrite (N_ascii_embedding (x mod 256)).
  rewrite (N_ascii_embedding (x / byte_range_size)).
  rewrite (div_mul_mod_ident n byte_range_size); auto.
  + easy.
  + 

*)
Theorem rrq_serial_ident : forall 

Theorem string_packet_ident : forall s p p2, serialize_packet p = s -> deserialize_packet s = Some p2 -> p = p2.
Proof with magics.
intros s p p2 SP DSP.
destruct p; destruct p2.
all: rewrite <- SP in DSP...
* cut (s0 = s1 /\ x = x0).
  { magic. rewrite H0. Show Proof. rewrite H1...
  unfold serialize_packet in DSP...
  unfold opcode_to_string in DSP...
  unfold word_no_to_string in DSP...
  unfold byte_range_size in DSP...
  unfold opcode_to_ascii in DSP...
  unfold two_ascii_to_string in DSP...
  unfold opcode_to_nr in DSP...
  unfold ascii_of_pos in DSP...
  unfold deserialize_packet in DSP...
  unfold ascii_to_opcode in DSP...
  destruct x...
  + simpl in DSP...
    unfold two_ascii_to_string in DSP...
    destruct x0...
    unfold  in DSP...
  
  
  
destruct p; rewrite <- H.
* unfold serialize_packet.
* unfold deserialize_packet; simpl; auto.
  rewrite <- H.
  simpl serialize_packet.
  unfold opcode_to_ascii.
  unfold opcode_to_nr.
  unfold ascii_of_pos.
  unfold ascii_to_opcode.
  simpl N_of_ascii.
  unfold nr_to_opcode.
  simpl .
    rewrite <- H.
    exfalso.




simpl. 
  unfold opcode_to_ascii.
  simpl.
  unfold ascii_of_pos. 
  unfold null_terminate.
  simpl.
  destruct (deserialize_packet s).
  + 
  
(* client *)



Record init_state : Set := mkState {
    transfer_mode : mode;
    filename : string;
    port: positive;
    last_packet : option packet;
    timeout_count : N;
}.

Definition coq_process_state () := .
