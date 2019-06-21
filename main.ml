#require "unix"

open Unix
open Printf
(*open client
  open packet*)

(* Auxiliary definitions *)

let compose f g x = f (g x);;

let exit_err msg = printf msg; exit 1;;

let assign_opt r v = r := Some v;;

let nr_to_char nr = Char.chr (Char.code '0' + nr);;

let char_to_nr c = Char.code c - Char.code '0';;

let max_packet_len = 514;;

let unwrap opt = match opt with Some x -> x | None -> exit_err "bad option access";;

(* Mutable state of the program *)

let address = ref None;; (* !address : string *)

let in_file_name = ref None;; (* !in_file_name  string *)

let out_file_name = ref None;; (* !out_file_name : string *)

type mode = Write | Read;;

let current_mode = ref None;; (* !current_mode : mode *)

let local_file = ref None;; (* !local_file : file_descr *)

let last_packet = ref Bytes.empty;;

let finished = ref false;;

(* Program arguments *)

let set_mode new_mode = 
  current_mode := match new_mode with
    | "read"  -> Some Read
    | "write" -> Some Write
    | _       -> exit_err "invalid file mode: must be read or write"
;;

let args = [
  ("-a", Arg.String (assign_opt address), "The address of the server.");
  ("-i", Arg.String (assign_opt in_file_name), "The name of the input file.");
  ("-o", Arg.String (assign_opt out_file_name), "The name of the input file.");
  ("-m", Arg.String set_mode, "The mode of file transfer, \"read\" or \"write\".")
];;

(* Network communication *)

let default_mode = "netascii";;

(* ONLY FOR TESTING!!! *)
type opcode_type = RRQ | WRQ | DATA | ACK | ERROR;;

let opcode_to_int t =
  match t with
    | RRQ   -> 1
    | WRQ   -> 2
    | DATA  -> 3
    | ACK   -> 4
    | ERROR -> 5
;;

let int_to_opcode num = 
  match num with
    | 1 -> RRQ
    | 2 -> WRQ
    | 3 -> DATA
    | 4 -> ACK
    | _ -> ERROR
;;
(* ONLY FOR TESTING!!! *)


let create_init_packet file_name opcode = 
  let name_len = String.length file_name in
  let packet = Bytes.create (2 + name_len + 1 + String.length default_mode + 1) in
    Bytes.set packet 0 '\000';
    Bytes.set packet 1 (Char.chr (opcode_to_int opcode));
    Bytes.blit_string file_name 0 packet 2 name_len;
    Bytes.set packet (2 + name_len) '\000';
    Bytes.blit_string default_mode 0 packet (2 + name_len + 1) (String.length default_mode);
    Bytes.set packet (Bytes.length packet - 1) '\000';
    packet
;;

let send_init fd addr = 
  let packet = if !current_mode = Read then
      create_init_packet in_file_name RRQ 
    else 
      create_init_packet out_file_name WRQ 
  in
    handle_unix_error sendto fd packet 0 (Bytes.length packet) [] addr;
    ()
;;

let receive_response fd =
  let buffer = Bytes.create max_packet_len in
  let len, _ = handle_unix_error recvfrom fd buffer 0 max_packet_len [] in
    (len, buffer)
;;

let process_response fd addr response = 
  match coq_advance_state response 
;;

let run_client info = 
  (* type addr_info = { 
     ai_family : socket_domain; 
     ai_socktype : socket_type; 
     ai_protocol : int; 
     ai_addr : sockaddr; 
     ai_canonname : string } *)
  let sock_fd = handle_unix_error socket info.ai_family info.ai_socktype info.ai_protocol in
    send_init fd info.ai_addr;
    while not !finished do
      let response = match select [] [sock_fd] [] 5.0 with
        | ([], [_], []) -> receive_response sock_fd
        | _ -> exit_err "The server timed out."
      in process_response fd info.ai_addr response
    done
;;

let first_ok f l = 
  match l with 
    | []     -> exit_err "Unknown error."
    | h :: t -> if not (f h) then first_ok f t
;;

let main () = 
  Arg.parse args (_ -> ()) "A simple TFTP client written in Coq written by Jacek Olczyk.";
  (*if !port < 0 || 65536 < !port then exit_err In*)
  if !mode = Read then 
    assign_opt local_file (handle_unix_error openfile !out_file_name [O_WRONLY; O_CREAT; O_EXCL] 0o755)
  else 
    assign_opt local_file (handle_unix_error openfile !in_file_name [O_RDONLY] 0);
  let addr_list = handle_unix_error getaddrinfo !address !port 
                    [AI_FAMILY PF_INET; AI_SOCKTYPE SOCK_DGRAM] in
    first_ok run_client addr_list
;;
