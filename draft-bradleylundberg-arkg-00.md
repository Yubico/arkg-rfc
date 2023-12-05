# DRAFT: The Asynchronous Remote Key Generation (ARKG) algorithm


## Abstract

This document specifies a generic algorithm for delegating generation of asymmetric key pairs
in such a way that the delegated party can generate any number of nondeterministic, unlinkable public keys,
while only the delegating party can derive the corresponding private keys.
The algorithm involves no shared secrets and is generic over the cryptographic primitives used.
Applications of this include generating "pseudonym" public keys to enhance privacy,
generating backup public keys and extending privileges to a trusted partner.


## Status of This Memo

TODO


## Copyright Notice

TODO


## Introduction

TODO: Define seed key pair, seed public key, seed private key


## The Asynchronous Remote Key Generation (ARKG) algorithm


### Notation

The following notation is used throughout this document:

- The symbol `||` represents octet string concatenation.

- When literal text strings are to be interpreted as octet strings,
  they are encoded using UTF-8.

- Elliptic curve operations are written in multiplicative notation:
  `*` denotes point multiplication, `^` denotes point exponentiation
  and `+` denotes scalar addition modulo the curve order.

- `Random(min_inc, max_exc)` represents a cryptographically secure random integer
  greater than or equal to `min_inc` and strictly less than `max_exc`.


### Instance parameters

ARKG is composed of a suite of other algorithms.
The parameters of an ARKG instance are:

- `BL`: An asymmetric key blinding scheme, consisting of:
  - Function `BL-Generate-Keypair() -> (pk, sk)`: Generate a blinding key pair.

    No input.

    Output consists of a blinding public key `pk` and a blinding secret key `sk`.

  - Function `BL-Blind-Public-Key(pk, tau) -> pk_tau`: Deterministically compute a blinded public key.

    Input consists of a blinding public key `pk` and a blinding factor `tau`.

    Output consists of the blinded public key `pk_tau`.

  - Function `BL-Blind-Secret-Key(sk, tau) -> sk_tau`: Deterministically compute a blinded secret key.

    Input consists of a blinding secret key `sk` and a blinding factor `tau`.

    Output consists of the blinded secret key `sk_tau`.

  - Integer `L_bl`: The length of the blinding factor `tau` in octets.

  `pk` and `pk_tau` are opaque octet strings of arbitrary length.
  `tau` is an opaque octet string of length `L_bl`.
  The representations of `sk`, `sk_tau` and `L_bl` are an undefined implementation detail.

- `KEM`: A key encapsulation mechanism, consisting of the functions:
  - `KEM-Generate-Keypair() -> (pk, sk)`: Generate a key encapsulation key pair.

    No input.

    Output consists of public key `pk` and secret key `sk`.

  - `KEM-Encaps(pk) -> (k, c)`: Generate a key encapsulation.

    Input consists of an encapsulation public key `pk`.

    Output consists of a shared secret `k` and an encapsulation ciphertext `c`.

  - `KEM-Decaps(sk, c) -> k`: Decapsulate a shared secret.

    Input consists of encapsulation secret key `sk` and encapsulation ciphertext `c`.

    Output consists of the shared secret `k` on success, or an error otherwise.

  `pk`, `k` and `c` are opaque octet strings.
  The representation of `sk` is an undefined implementation detail.

- `MAC`: A message authentication code (MAC) scheme, consisting of:
  - Function `MAC-Tag(k, m) -> t`: Generate a message authentication tag for a given message using a given key.

    Input consists of the shared MAC key `k` and the message `m`.

    Output consists of the MAC tag `t`.

  - Function `MAC-Verify(k, m, t) -> { 0, 1 }`: Verify a message authentication tag.

    Input consists of the shared MAC key `k`, the message `m` and the MAC tag `t`.

    Output is 1 if and only if `MAC-Tag(k, m) = t`.

  - Integer `L_mac`: The length of the MAC key `k` in octets.

  `k` is an opaque octet string of length `L_mac`.
  `m` and `t` are opaque octet strings of arbitrary length.
  The representation of `L_mac` is an undefined implementation detail.

- `KDF`: A variable-length key derivation function with the signature:
  `KDF(info, ikm, L) -> okm`

  Input consists of a domain separation parameter `info`, input key material `ikm` and output length `L`.

  Output consists of output key material `okm` of length `L` in octets.

  `info` and `ikm` are opaque octet strings of arbitrary length.
  `okm` is an opaque octet string of length `L`.
  `L` is an integer with undefined representation.

A concrete ARKG instantiation MUST specify the instantiation
of each of the above functions and values.

The output keys of the `BL` scheme are also the output keys of the ARKG instance as a whole.
For example, if `BL-Blind-Public-Key` and `BL-Blind-Secret-Key` output ECDSA keys,
then the ARKG instance will also output ECDSA keys.

Instantiations MUST satisfy the following compatibility criteria:

- The output shared secret `k` of `KEM-Encaps` and `KEM-Decaps`
  is a valid input key material `ikm` of `KDF`.

- Output key material `okm` of length `L_bl` of `KDF`
  is a valid input blinding factor `tau` of `BL-Blind-Public-Key` and `BL-Blind-Secret-Key`.

  It is permissible for some `KDF` outputs to not be valid blinding factors,
  as long as this happens with negligible probability -
  see section [Design Rationale: Using a MAC].

- Output key material `okm` of length `L_mac` of `KDF`
  is a valid input MAC key `k` of `MAC-Tag(k, m)` and `MAC-Verify(k, m, t)`.

  It is permissible for some `KDF` outputs to not be valid MAC keys,
  as long as this happens with negligible probability -
  see section [Design Rationale: Using a MAC].

We denote a concrete ARKG instance by the pattern `ARKG-BL-KEM-MAC-KDF`,
substituting the chosen instantiation for the `BL`, `KEM`, `MAC` and `KDF` parts.


### The function ARKG-Generate-Seed

This function is performed by the holder of the ARKG seed private key `sk`.
The resulting ARKG seed public key `pk` is provided to the delegate party
which will then be able to generate public keys on behalf of the holder of `sk`.

```
ARKG-Generate-Seed() -> (pk, sk)
    Options:
        BL         The key blinding scheme chosen for the ARKG instantiation.
        KEM        The key encapsulation mechanism chosen for the ARKG instantiation.

    Inputs: None

    Output:
        (pk, sk)   An ARKG seed key pair with public key pk and private key sk.

   The output (pk, sk) is calculated as follows:

   (pk_kem, sk_kem) = KEM-Generate-Keypair()
   (pk_bl, sk_bl) = BL-Generate-Keypair()
   pk = (pk_kem, pk_bl)
   sk = (sk_kem, sk_bl)
```


### The function ARKG-Derive-Public-Key

This function is performed by the holder of the ARKG seed public key `(pk_kem, pk_bl)`.
The resulting public key `pk'` can be provided to external parties to use in asymmetric cryptography protocols.
The resulting key handle `kh` can be used by the holder of the ARKG seed private key
to derive the private key corresponding to `pk'`.

```
ARKG-Derive-Public-Key((pk_kem, pk_bl), info) -> (pk', kh)
    Options:
        BL         The key blinding scheme chosen for the ARKG instantiation.
        KEM        The key encapsulation mechanism chosen for the ARKG instantiation.
        MAC        The MAC scheme chosen for the ARKG instantiation.
        KDF        The key derivation function chosen for the ARKG instantiation.
        L_bl       The length in octets of the blinding factor tau of the key blinding scheme BL.
        L_mac      The length in octets of the MAC key of the MAC scheme MAC.

    Inputs:
        pk_kem     A key encapsulation public key.
        pk_bl      A key blinding public key.
        info       Optional context and application specific information (can be a zero-length string).

    Output:
        pk'        A blinded public key.
        kh         A key handle for deriving the blinded secret key sk' corresponding to pk'.

    The output (pk, sk) is calculated as follows:

    (k, c) = KEM-Encaps(pk_kem)
    tau = KDF("arkg-blind" || 0x00 || info, k, L_bl)
    mk  = KDF("arkg-mac"   || 0x00 || info, k, L_mac)
    tag = MAC-Tag(mk, c || info)

    pk' = BL-Blind-Public-Key(pk_bl, tau)
    kh = (c, tag)
```

If this procedure aborts due to an error,
for example because `KDF` returns an invalid `tau` or `mk`,
the procedure can safely be retried with the same arguments.


### The function ARKG-Derive-Secret-Key

This function is performed by the holder of the ARKG seed private key `(sk_kem, sk_bl)`.
The resulting secret key `sk'` can be used in asymmetric cryptography protocols
to prove possession of `sk'` to an external party that has the corresponding public key.

```
ARKG-Derive-Secret-Key((sk_kem, sk_bl), kh, info) -> sk'
    Options:
        BL         The key blinding scheme chosen for the ARKG instantiation.
        KEM        The key encapsulation mechanism chosen for the ARKG instantiation.
        MAC        The MAC scheme chosen for the ARKG instantiation.
        KDF        The key derivation function chosen for the ARKG instantiation.
        L_bl       The length in octets of the blinding factor tau of the key blinding scheme BL.
        L_mac      The length in octets of the MAC key of the MAC scheme MAC.

    Inputs:
        sk_kem     A key encapsulation secret key.
        sk_bl      A key blinding secret key.
        kh         A key handle output from ARKG-Derive-Public-Key.
        info       Optional context and application specific information (can be a zero-length string).

    Output:
        sk'        A blinded secret key.

    The output sk' is calculated as follows:

    (c, tag) = kh
    k = KEM-Decaps(sk_kem, c)
    mk = KDF("arkg-mac" || 0x00 || info, k, L_mac)

    If MAC-Verify(mk, c || info, tag) = 0:
        Abort with an error.

    tau = KDF("arkg-blind" || 0x00 || info, k, L_bl)
    sk' = BL-Blind-Secret-Key(sk_bl, tau)
```

Errors in this procedure are typically unrecoverable.
For example, `KDF` might return an invalid `tau` or `mk`, or the `tag` may be invalid.
ARKG instantiations SHOULD be chosen in a way that such errors are impossible
if `kh` was generated by an honest and correct implementation of `ARKG-Derive-Public-Key`.
Incorrect or malicious implementations of `ARKG-Derive-Public-Key` do not degrade the security
of a correct and honest implementation of `ARKG-Derive-Secret-Key`.
See also section [Design Rationale: Using a MAC].


## Generic ARKG instantiations

This section defines generic formulae for instantiating the individual ARKG parameters,
which can be used to define concrete ARKG instantiations.

TODO: IANA registry? COSE/JOSE?


### Using elliptic curve arithmetic for key blinding

Instantiations of ARKG whose output keys are elliptic curve keys
can use elliptic curve arithmetic as the key blinding scheme `BL`. [Frymann] [Wilson]
This section defines a general formula for such instantiations of `BL`.

Let `crv` be an elliptic curve.
Then the `BL` parameter of ARKG may be instantiated as follows:

- Elliptic curve points are encoded to and from octet strings
  using the procedures defined in sections 2.3.3 and 2.3.4 of [SEC 1][sec1].

- Elliptic curve scalar values are encoded to and from octet strings
  using the procedures defined in sections 2.3.7 and 2.3.8 of [SEC 1][sec1].

- `N` is the order of `crv`.
- `G` is the generator of `crv`.

```
BL-Generate-Keypair() -> (pk, sk)

    sk = Random(1, N)
    pk = G^sk
    If pk equals the point at infinity, abort with an error.

    TODO: Also reject G?


BL-Blind-Public-Key(pk, tau) -> pk_tau

    If tau = 0 or tau >= N, abort with an error.
    pk_tau = pk * (G^tau)
    If pk_tau equals the point at infinity, abort with an error.

    TODO: Also reject G?


BL-Blind-Secret-Key(sk, tau) -> sk_tau

    If tau = 0 or tau >= N, abort with an error.
    sk_tau = sk + tau
    If sk_tau = 0, abort with an error.

    TODO: Also reject 1?
```


### Using ECDH as the KEM

Instantiations of ARKG can use ECDH [RFC6090] as the key encapsulation mechanism.
This section defines a general formula for such instantiations of `KEM`.

Let `crv` be an elliptic curve used for ECDH.
Then the `KEM` parameter of ARKG may be instantiated as follows:

- Elliptic curve points are encoded to and from octet strings
  using the procedures defined in sections 2.3.3 and 2.3.4 of [SEC 1][sec1].

- Elliptic curve coordinate field elements are encoded to and from octet strings
  using the procedures defined in sections 2.3.5 and 2.3.6 of [SEC 1][sec1].

- Elliptic curve scalar values are encoded to and from octet strings
  using the procedures defined in sections 2.3.7 and 2.3.8 of [SEC 1][sec1].

- `ECDH(pk, sk)` represents the compact output of ECDH [RFC6090]
  using public key (curve point) `pk` and secret key (exponent) `sk`.

- `N` is the order of `crv`.
- `G` is the generator of `crv`.

```
KEM-Generate-Keypair() -> (pk, sk)

    sk = Random(1, N)
    pk = G^sk
    If pk equals the point at infinity, abort with an error.

    TODO: Also reject G?


KEM-Encaps(pk) -> (k, c)
    (pk', sk') = KEM-Generate-Keypair()

    k = ECDH(pk, sk')
    c = pk'


KEM-Decaps(sk, c) -> k

    pk' = c
    k = ECDH(pk', sk)
```


### Using both elliptic curve arithmetic for key blinding and ECDH as the KEM

If elliptic curve arithmetic is used for key blinding and ECDH is used as the KEM,
as described in the previous sections,
then both of them MAY use the same curve or MAY use different curves.
If both use the same curve, then it is also possible to use the same public key
as both the key blinding public key and the KEM public key. [Frymann]

TODO: Caveats? I think I read in some paper or thesis about specific drawbacks of using the same key for both.


### Using HMAC as the MAC

Let `Hash` be a cryptographic hash function.
Then the `MAC` parameter of ARKG may be instantiated as follows:

```
MAC-Tag(k, m) -> t

    t = HMAC-Hash(K=k, text=m)


MAC-Verify(k, m, t) -> { 0, 1 }

    t' = HMAC-Hash(K=k, text=m)
    If t = t':
        return 1
    Else:
        return 0
```


### Using HKDF as the KDF

Let `Hash` be a cryptographic hash function.
Then the `KDF` parameter of ARKG may be instantiated as follows:

```
KDF(info, ikm, L) -> okm

    PRK = HKDF-Extract with the arguments:
        Hash: Hash
        salt: not set
        IKM: ikm

    okm = HKDF-Expand with the arguments:
        Hash: Hash
        PRK: PRK
        info: info
        L: L
```


## Concrete ARKG instantiations

This section defines an initial set of concrete ARKG instantiations.

TODO: IANA registry? COSE/JOSE?


#### ARKG-P256-ECDH-P256-HMAC-SHA256-HKDF-SHA256

The identifier `ARKG-P256-ECDH-P256-HMAC-SHA256-HKDF-SHA256` represents the following ARKG instantiation:

- `BL`: Elliptic curve arithmetic on the NIST curve `secp256r1` as described in section [Using elliptic curve arithmetic for key blinding].
- `KEM`: [ECDH][RFC6090] on the NIST curve `secp256r1` as described in section [Using ECDH as the KEM].
- `MAC`: HMAC using SHA-256 as described in section [Using HMAC as the MAC].
- `KDF`: HKDF using SHA-256 as described in section [Using HKDF as the KDF].
- `L_bl`: 32
- `L_mac`: 32


#### ARKG-P384-ECDH-P384-HMAC-SHA384-HKDF-SHA384

The identifier `ARKG-P384-ECDH-P384-HMAC-SHA384-HKDF-SHA384` represents the following ARKG instantiation:

- `BL`: Elliptic curve arithmetic on the NIST curve `secp384r1` as described in section [Using elliptic curve arithmetic for key blinding].
- `KEM`: [ECDH][RFC6090] on the NIST curve `secp384r1` as described in section [Using ECDH as the KEM].
- `MAC`: HMAC using SHA-384 as described in section [Using HMAC as the MAC].
- `KDF`: HKDF using SHA-384 as described in section [Using HKDF as the KDF].
- `L_bl`: 48
- `L_mac`: 48


#### ARKG-P521-ECDH-P521-HMAC-SHA512-HKDF-SHA512

The identifier `ARKG-P521-ECDH-P521-HMAC-SHA512-HKDF-SHA512` represents the following ARKG instantiation:

- `BL`: Elliptic curve arithmetic on the NIST curve `secp521r1` as described in section [Using elliptic curve arithmetic for key blinding].
- `KEM`: [ECDH][RFC6090] on the NIST curve `secp521r1` as described in section [Using ECDH as the KEM].
- `MAC`: HMAC using SHA-512 as described in section [Using HMAC as the MAC].
- `KDF`: HKDF using SHA-512 as described in section [Using HKDF as the KDF].
- `L_bl`: 64
- `L_mac`: 64


#### ARKG-P256k-ECDH-P256k-HMAC-SHA256-HKDF-SHA256

The identifier `ARKG-P256k-ECDH-P256k-HMAC-SHA256-HKDF-SHA256` represents the following ARKG instantiation:

- `BL`: Elliptic curve arithmetic on the SECG curve `secp256k1` as described in section [Using elliptic curve arithmetic for key blinding].
- `KEM`: [ECDH][RFC6090] on the SECG curve `secp256k1` as described in section [Using ECDH as the KEM].
- `MAC`: HMAC using SHA-256 as described in section [Using HMAC as the MAC].
- `KDF`: HKDF using SHA-256 as described in section [Using HKDF as the KDF].
- `L_bl`: 32
- `L_mac`: 32


#### ARKG-Ed25519-X25519-HMAC-SHA256-HKDF-SHA256

The identifier `ARKG-Ed25519-X25519-HMAC-SHA256-HKDF-SHA256` represents the following ARKG instantiation:

- `BL`: Elliptic curve arithmetic on the curve `Ed25519` as described in section [Using elliptic curve arithmetic for key blinding].
- `KEM`: [ECDH][RFC6090] on the NIST curve `X25519` as described in section [Using ECDH as the KEM].
- `MAC`: HMAC using SHA-256 as described in section [Using HMAC as the MAC].
- `KDF`: HKDF using SHA-256 as described in section [Using HKDF as the KDF].
- `L_bl`: 32
- `L_mac`: 32


#### ARKG-X25519-X25519-HMAC-SHA256-HKDF-SHA256

The identifier `ARKG-X25519-X25519-HMAC-SHA256-HKDF-SHA256` represents the following ARKG instantiation:

- `BL`: Elliptic curve arithmetic on the curve `X25519` as described in section [Using elliptic curve arithmetic for key blinding].
- `KEM`: [ECDH][RFC6090] on the NIST curve `X25519` as described in section [Using ECDH as the KEM].
- `MAC`: HMAC using SHA-256 as described in section [Using HMAC as the MAC].
- `KDF`: HKDF using SHA-256 as described in section [Using HKDF as the KDF].
- `L_bl`: 32
- `L_mac`: 32


## Security Considerations

TODO


## Privacy Considerations

TODO


## IANA Considerations

TODO


## Design rationale

### Using a MAC

WIP:

[Wilson] omits the MAC and instead encodes application context in the PRF labels,
arguing this leads to invalid keys/signatures in cases that would have a bad MAC.
We choose to keep the MAC so that `ARKG-Derive-Secret-Key` can be assured
that no unrecoverable errors will happen (for example out-of-range EC scalars/infinity points, etc.),
and any retry logic is done exclusively by the `ARKG-Derive-Public-Key` party.
For example, key generation might be done by randomly testing candidates [NIST.SP.800-56Ar3]].
In this case the MAC enables `ARKG-Derive-Secret-Key` to assume
that the first candidate will be successful, and just fail otherwise.
`ARKG-Derive-Public-Key` is likely to run on powerful general-purpose hardware, such as a laptop or smartphone,
while `ARKG-Derive-Secret-Key` might run on more constrained hardware such as a cryptographic smart card,
which benefit greatly from such optimizations.


## Implementation Status

TODO


## References

TODO

Closely related previous work:
- Emil Lundberg and Dain Nilsson, "WebAuthn recovery extension". GitHub, 2019-2021.
  https://github.com/Yubico/webauthn-recovery-extension
- Frymann et al., "Asynchronous Remote Key Generation: An Analysis of Yubico's Proposal for W3C WebAuthn".
  Proceedings of the 2020 ACM SIGSAC Conference on Computer and Communications Security, 2020.
  https://doi.org/10.1145/3372297.3417292


[arkg]: https://doi.org/10.1145/3372297.3417292
[att-cred-data]: https://w3c.github.io/webauthn/#attested-credential-data
[authdata]: https://w3c.github.io/webauthn/#authenticator-data
[ctap2-canon]: https://fidoalliance.org/specs/fido-v2.0-ps-20190130/fido-client-to-authenticator-protocol-v2.0-ps-20190130.html#ctap2-canonical-cbor-encoding-form
[hkdf]: https://tools.ietf.org/html/rfc5869
[privacy-cons]: https://www.w3.org/TR/2019/WD-webauthn-2-20191126/#sctn-credential-id-privacy-leak
[rfc3279]: https://tools.ietf.org/html/rfc3279.html
[rp-auth-ext-processing]: https://w3c.github.io/webauthn/#sctn-verifying-assertion
[rp-reg-ext-processing]: https://w3c.github.io/webauthn/#sctn-registering-a-new-credential
[sec1]: http://www.secg.org/sec1-v2.pdf


## Acknowledgements

The authors would like to thank Dain Nilsson for the original proposal [WEBAUTHN-RECOVERY-EXTENSION] that eventually led to this RFC,
and Pieter Wuille for [BIP32] which in turn served as an inspiration to Dain.


## Appendix A. Test Vectors

TODO


## Authors' Addresses

Emil Lundberg
Yubico
Kungsgatan 44
111 37 Stockholm
Sweden

Phone: (+46) 73 247 30 62
EMail: emil@yubico.com
EMail: emil@emlun.se


John Bradley
Yubico
TODO

Phone: TODO
EMail: TODO
