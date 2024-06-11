open Mirage_crypto_pk
open Mirage_crypto
open Configuration.Config

type public_key = Dsa.pub
type private_key = Dsa.priv
type signature = Cstruct.t * Cstruct.t

let signature_equal ((r1, s1) : signature) ((r2, s2) : signature) =
  (Cstruct.equal r1 r2) && (Cstruct.equal s1 s2)

let pub_key_map : (address, public_key) Hashtbl.t = Hashtbl.create 32

let generate_keys : (public_key * private_key) lazy_t =
  lazy (Mirage_crypto_rng_unix.initialize (module Mirage_crypto_rng.Fortuna);
    let priv = Dsa.generate `Fips2048 in
    let pub = Dsa.pub_of_priv priv in
    (* also add into the hash table *)
    let _ = Hashtbl.add pub_key_map (!me_ip, !me_port) pub in
    (pub, priv))

let self_pub_key () : public_key = fst (Lazy.force generate_keys)

let self_priv_key () : private_key = snd (Lazy.force generate_keys)

(* NOTE: cannot 100% guarantee that this is the correct way of signing things. maybe someone else could audit this *)
let sign_string (s : string) (priv : private_key) : signature =
  let msg = Cstruct.of_string s in
  let hmsg = Hash.digest `SHA256 msg in
  let rs = Dsa.sign ~key:priv hmsg in
  rs
  
(* implementing `verify_string` here will introduce a dependency cycle, so it is in companion/Common.ml *)