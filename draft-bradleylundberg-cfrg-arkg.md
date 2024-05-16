---
stand_alone: true
ipr: trust200902

title: The Asynchronous Remote Key Generation (ARKG) algorithm
abbrev: "ARKG"
lang: en
category: info

docname: draft-bradleylundberg-cfrg-arkg-latest
submissiontype: IETF  # also: "independent", "editorial", "IAB", or "IRTF"
number:
date:
consensus: true
v: 3
area: "IRTF"
workgroup: "Crypto Forum"
keyword:
 - KDF
venue:
  group: "Crypto Forum"
  type: "Research Group"
  github: "Yubico/arkg-rfc"


author:
- role: editor
  fullname: Emil Lundberg
  organization: Yubico
  street: Kungsgatan 44
  city: Stockholm
  country: SE
  email: emil@emlun.se

- fullname: John Bradley
  organization: Yubico
  email: ve7jtb@ve7jtb.com

contributor:
  fullname: Dain Nilsson
  organization: Yubico

normative:
  RFC2104:
  RFC4949:
  RFC5869:
  RFC6090:
  RFC7748:
  RFC8032:
  RFC8610:
  RFC9380:
  SEC1:
    target: http://www.secg.org/sec1-v2.pdf
    author:
    - org: Certicom Research
    date: 2009
    title: 'SEC 1: Elliptic Curve Cryptography'
  SEC2:
    target: http://www.secg.org/sec2-v2.pdf
    author:
    - org: Certicom Research
    date: 2010
    title: 'SEC 2: Recommended Elliptic Curve Domain Parameters'

informative:
  BIP32:
    target: https://github.com/bitcoin/bips/blob/master/bip-0032.mediawiki
    title: BIP 32 Hierarchical Deterministic Wallets
    author:
    - name: Pieter Wuille
    date: 2012
  Clermont:
    target: https://www.cryptoplexity.informatik.tu-darmstadt.de/media/crypt/teaching_1/theses_1/Sebastian_Clermont_Thesis.pdf
    author:
    - name: Sebastian A. Clermont
    - org: "Technische Universität Darmstadt"
    date: 2022
    title: "Post Quantum Asynchronous Remote Key Generation. Master's thesis"
  WebAuthn-Recovery:
    author:
    - name: Emil Lundberg
    - name: Dain Nilsson
    title: "WebAuthn recovery extension: Asynchronous delegated key generation without shared secrets. GitHub"
    date: 2019
    target: https://github.com/Yubico/webauthn-recovery-extension
  Frymann2020:
    author:
    - name: Nick Frymann
    - name: Daniel Gardham
    - name: Franziskus Kiefer
    - name: Emil Lundberg
    - name: Mark Manulis
    - name: Dain Nilsson
    title: "Asynchronous Remote Key Generation: An Analysis of Yubico's Proposal for W3C WebAuthn. CCS '20: Proceedings of the 2020 ACM SIGSAC Conference on Computer and Communications Security"
    date: 2020
    target: https://eprint.iacr.org/2020/1004
  Frymann2023:
    author:
    - name: Nick Frymann
    - name: Daniel Gardham
    - name: Mark Manulis
    title: Asynchronous Remote Key Generation for Post-Quantum Cryptosystems from Lattices. 2023 IEEE 8th European Symposium on Security and Privacy
    date: 2023
    target: https://eprint.iacr.org/2023/419
  Wilson:
    author:
    - name: Spencer MacLaren Wilson
    - org: University of Waterloo,
    title: "Post-Quantum Account Recovery for Passwordless Authentication. Master's thesis"
    date: 2023
    target: http://hdl.handle.net/10012/19316



--- abstract

Asynchronous Remote Key Generation (ARKG) is an abstract algorithm
that enables delegation of asymmetric public key generation without giving access to the corresponding private keys.
This capability enables a variety of applications:
a user agent can generate pseudonymous public keys to prevent tracking;
a message sender can generate ephemeral recipient public keys to enhance forward secrecy;
two paired authentication devices can each have their own private keys while each can register public keys on behalf of the other.

This document provides three main contributions:
a specification of the generic ARKG algorithm using abstract primitives;
a set of formulae for instantiating the abstract primitives using concrete primitives;
and an initial set of fully specified concrete ARKG instances.
We expect that additional instances will be defined in the future.



--- middle

{:emlun: source="Emil"}

# Introduction

Asynchronous Remote Key Generation (ARKG) introduces a mechanism
to generate public keys without access to the corresponding private keys.
Such a mechanism is useful for many scenarios when a new public key is needed
but the private key holder is not available to perform the key generation.
This may occur when private keys are stored in a hardware security device,
which may be unavailable or locked at the time a new public key is needed.

Some motivating use cases of ARKG include:

- __Single-use asymmetric keys__:
  Envisioned for the European Union's digital identity framework,
  which is set to use single-use asymmetric keys to prevent colluding verifiers from using public keys as correlation handles.
  Each digital identity credential would thus be issued with a single-use proof-of-possession key,
  used only once to present the credential to a verifier.
  ARKG empowers both online and offline usage scenarios:
  for offline scenarios, ARKG enables pre-generation of public keys for single-use credentials
  without needing to access the hardware security device that holds the private keys.
  For online scenarios, ARKG gives the credential issuer assurance
  that all derived private keys are bound to the same secure hardware element.
  In both cases, application performance may be improved
  since public keys can be generated in a general-purpose execution environment instead of a secure enclave.

- __Enhanced forward secrecy__:
  The use of ARKG can facilitate forward secrecy in certain contexts.
  For instance, [section 8.5.4 of RFC 9052][rfc9052-direct-key-agreement] notes that
  "Since COSE is designed for a store-and-forward environment rather than an online environment,
  \[...\] forward secrecy (see [RFC4949]) is not achievable. A static key will always be used for the receiver of the COSE object."
  As opposed to workarounds like exchanging a large number of keys in advance,
  ARKG enables the the sender to generate ephemeral recipient public keys on demand.

- __Backup key generation__:
  For example, the W3C Web Authentication API [WebAuthn] (WebAuthn) generates a new key pair for each account on each web site.
  ARKG could allow for simultaneously generating a backup public key when registering a new public key.
  A primary authenticator could generate both a key pair for itself and a public key for a paired backup authenticator.
  The backup authenticator only needs to be paired with the primary authenticator once,
  and can then be safely stored until it is needed.

ARKG consists of three procedures:

- __Initialization__:
  The _delegating party_ generates a _seed pair_ and discloses the _public seed_ to a _subordinate party_,
  while securely retaining the _private seed_.
- __Public key generation__:
  The subordinate party uses the public seed to autonomously generate a new public key
  along with a unique _key handle_ for the public key.
  This can be repeated any number of times.
- __Private key derivation__:
  The delegating party uses a key handle and the private seed
  to derive the private key corresponding to the public key generated along with the key handle.
  This can be repeated with any number of key handles.

Notably, ARKG can be built entirely using established cryptographic primitives.
The required primitives are a public key blinding scheme and a key encapsulation mechanism (KEM),
which may in turn use a key derivation function (KDF) and a message authentication code (MAC) scheme.
Both conventional primitives and quantum-resistant alternatives exist that meet these requirements. [Wilson]


[rfc9052-direct-key-agreement]: https://www.rfc-editor.org/rfc/rfc9052.html#name-direct-key-agreement


## Requirements Language

{::boilerplate bcp14-tagged}


## Notation

The following notation is used throughout this document:

- The symbol `||` represents octet string concatenation.

- Literal text strings and octet strings are denoted
  using the CDDL syntax defined in {{Section 3.1 of RFC8610}}.

- Elliptic curve operations are written in additive notation:
  `+` denotes point addition, i.e., the curve group operation;
  `*` denotes point multiplication, i.e., repeated point addition;
  and `+` also denotes scalar addition modulo the curve order.
  `*` has higher precedence than `+`, i.e., `a + b * C` is equivalent to `a + (b * C)`.


# The Asynchronous Remote Key Generation (ARKG) algorithm

The ARKG algorithm consists of three functions, each performed by one of two participants:
the _delegating party_ or the _subordinate party_.
The delegating party generates an ARKG _seed pair_ and emits the _public seed_ to the subordinate party
while keeping the _private seed_ secret.
The subordinate party can then use the public seed to generate derived public keys and _key handles_,
and the delegating party can use the private seed and a key handle to derive the corresponding private key.

The following subsections define the abstract instance parameters used to construct the three ARKG functions,
followed by the definitions of the three ARKG functions.


## Instance parameters {#arkg-params}

ARKG is composed of a suite of other algorithms.
The parameters of an ARKG instance are:

- `BL`: An asymmetric key blinding scheme [Wilson], consisting of:
  - Function `BL-Generate-Keypair() -> (pk, sk)`: Generate a blinding key pair.

    No input.

    Output consists of a blinding public key `pk` and a blinding private key `sk`.

  - Function `BL-Blind-Public-Key(pk, tau) -> pk_tau`: Deterministically compute a blinded public key.

    Input consists of a blinding public key `pk` and a blinding factor `tau`.

    Output consists of the blinded public key `pk_tau`.

  - Function `BL-Blind-Private-Key(sk, tau) -> sk_tau`: Deterministically compute a blinded private key.

    Input consists of a blinding private key `sk` and a blinding factor `tau`.

    Output consists of the blinded private key `sk_tau`.

  `tau` is an opaque octet string of arbitrary length.
  The representations of `pk` and `pk_tau` are defined by the protocol that invokes ARKG.
  The representations of `sk` and `sk_tau` are an undefined implementation detail.

  See [Wilson] for definitions of security properties required of the key blinding scheme `BL`.

- `KEM`: A key encapsulation mechanism, consisting of the functions:
  - `KEM-Generate-Keypair() -> (pk, sk)`: Generate a key encapsulation key pair.

    No input.

    Output consists of public key `pk` and private key `sk`.

  - `KEM-Encaps(pk, info) -> (k, c)`: Generate a key encapsulation.

    Input consists of an encapsulation public key `pk`
    and a domain separation parameter `info`.
    `info` is an opaque octet string of arbitrary length.

    Output consists of a shared secret `k` and an encapsulation ciphertext `c`.

  - `KEM-Decaps(sk, c, info) -> k`: Decapsulate a shared secret.

    Input consists of encapsulation private key `sk`, encapsulation ciphertext `c`
    and a domain separation parameter `info`.
    `info` is an opaque octet string of arbitrary length.

    Implementations MAY ignore the domain separation parameter `info`.

    Output consists of the shared secret `k` on success, or an error otherwise.

  `k` and `c` are opaque octet strings.
  The representation of `pk` is defined by the protocol that invokes ARKG.
  The representation of `sk` is an undefined implementation detail.

  See [Wilson] for definitions of additional security properties required of the key encapsulation mechanism `KEM`.

A concrete ARKG instantiation MUST specify the instantiation
of each of the above functions and values.

The output keys of the `BL` scheme are also the output keys of the ARKG instance as a whole.
For example, if `BL-Blind-Public-Key` and `BL-Blind-Private-Key` output ECDSA keys,
then the ARKG instance will also output ECDSA keys.

We denote a concrete ARKG instance by the pattern `ARKG-BL-KEM`,
substituting the chosen instantiation for the `BL` and `KEM`.
Note that this pattern cannot in general be unambiguously parsed;
implementations MUST NOT attempt to construct an ARKG instance by parsing such a pattern string.
Concrete ARKG instances MUST always be identified by lookup in a registry of fully specified ARKG instances.
This is to prevent usage of algorithm combinations that may be incompatible or insecure.


## The function ARKG-Generate-Seed

This function is performed by the delegating party.
The delegating party generates the ARKG seed pair `(pk, sk)`
and keeps the private seed `sk` secret, while the public seed `pk` is provided to the subordinate party.
The subordinate party will then be able to generate public keys on behalf of the delegating party.

~~~pseudocode
ARKG-Generate-Seed() -> (pk, sk)
    ARKG instance parameters:
        BL        A key blinding scheme.
        KEM       A key encapsulation mechanism.

    Inputs: None

    Output:
        (pk, sk)  An ARKG seed pair with public seed pk
                    and private seed sk.

    The output (pk, sk) is calculated as follows:

    (pk_kem, sk_kem) = KEM-Generate-Keypair()
    (pk_bl, sk_bl) = BL-Generate-Keypair()
    pk = (pk_kem, pk_bl)
    sk = (sk_kem, sk_bl)
~~~

### Deterministic key generation

Although the above definition expresses the key generation as opaque,
likely sampling uniformly random key distributions,
implementations MAY choose to implement the functions `BL-Generate-Keypair()`,
`KEM-Generate-Keypair()` and `ARKG-Generate-Seed()`
as deterministic functions of some out-of-band input.
This can be thought of as defining a single-use ARKG instance where these function outputs are static.
This use case is beyond the scope of this document
since the implementation of `ARKG-Generate-Seed` is internal to the delegating party,
even if applications choose to distribute the delegating party across multiple processing entities.

For example, one entity may randomly sample `pk_bl`, derive `pk_kem` deterministically from `pk_bl`
and submit only `pk_bl` to a separate service that uses the same procedure to also derive the same `pk_kem`.
This document considers both of these entities as parts of the same logical delegating party.


## The function ARKG-Derive-Public-Key

This function is performed by the subordinate party, which holds the ARKG public seed `pk = (pk_kem, pk_bl)`.
The resulting public key `pk'` can be provided to external parties to use in asymmetric cryptography protocols,
and the resulting key handle `kh` can be used by the delegating party to derive the private key corresponding to `pk'`.

This function may be invoked any number of times with the same public seed,
in order to generate any number of public keys.

~~~pseudocode
ARKG-Derive-Public-Key((pk_kem, pk_bl), info) -> (pk', kh)
    ARKG instance parameters:
        BL        A key blinding scheme.
        KEM       A key encapsulation mechanism.

    Inputs:
        pk_kem    A key encapsulation public key.
        pk_bl     A key blinding public key.
        info      An octet string containing optional context
                    and application specific information
                    (can be a zero-length string).

    Output:
        pk'       A blinded public key.
        kh        A key handle for deriving the blinded
                    private key sk' corresponding to pk'.

    The output (pk', kh) is calculated as follows:

    (tau, c) = KEM-Encaps(pk_kem, info)
    pk' = BL-Blind-Public-Key(pk_bl, tau)
    kh = c
~~~

If this procedure aborts due to an error,
the procedure can safely be retried with the same arguments.


## The function ARKG-Derive-Private-Key

This function is performed by the delegating party, which holds the ARKG private seed `(sk_kem, sk_bl)`.
The resulting private key `sk'` can be used in asymmetric cryptography protocols
to prove possession of `sk'` to an external party that has the corresponding public key.

This function may be invoked any number of times with the same private seed,
in order to derive the same or different private keys any number of times.

~~~pseudocode
ARKG-Derive-Private-Key((sk_kem, sk_bl), kh, info) -> sk'
    ARKG instance parameters:
        BL        A key blinding scheme.
        KEM       A key encapsulation mechanism.

    Inputs:
        sk_kem    A key encapsulation private key.
        sk_bl     A key blinding private key.
        kh        A key handle output from ARKG-Derive-Public-Key.
        info      An octet string containing optional context
                    and application specific information
                    (can be a zero-length string).

    Output:
        sk'       A blinded private key.

    The output sk' is calculated as follows:

    tau = KEM-Decaps(sk_kem, kh, info)
    If decapsulation failed:
        Abort with an error.

    sk' = BL-Blind-Private-Key(sk_bl, tau)
~~~

Errors in this procedure are typically unrecoverable.
For example, `KEM-Decaps` may fail to decapsulate the KEM ciphertext `kh` if it fails an integrity check.
ARKG instantiations SHOULD be chosen in a way that such errors are impossible
if `kh` was generated by an honest and correct implementation of `ARKG-Derive-Public-Key`.
Incorrect or malicious implementations of `ARKG-Derive-Public-Key` do not degrade the security
of a correct and honest implementation of `ARKG-Derive-Private-Key`.
See also {{arkg-seed-id}} and {{arkg-seed-correlation}}.


# Generic ARKG instantiations

This section defines generic formulae for instantiating the individual ARKG parameters,
which can be used to define concrete ARKG instantiations.


## Using elliptic curve addition for key blinding {#blinding-ec}

Instantiations of ARKG whose output keys are elliptic curve keys
can use elliptic curve addition as the key blinding scheme `BL` [Frymann2020]&nbsp;[Wilson].
This section defines a general formula for such instantiations of `BL`.

This formula has the following parameters:

- `crv`: An elliptic curve.
- `hash-to-crv-suite`: A hash-to-curve suite [RFC9380]
  suitable for hashing to the scalar field of `crv`.
- `hash-to-field-DST`: A domain separation tag satisfying the requirements stated in {{Section 3.1 of RFC9380}}.

Then the `BL` parameter of ARKG may be instantiated as follows:

- `G` is the generator of the prime order subgroup of `crv`.
- `N` is the order of `G`.
- The function `hash_to_field` is defined in {{Section 5 of RFC9380}}.

~~~pseudocode
BL-Generate-Keypair() -> (pk, sk)

    Generate (pk, sk) using some procedure defined for the curve crv.


BL-Blind-Public-Key(pk, tau, info) -> pk_tau

    tau' = hash_to_field(tau, 1) with the parameters:
        DST: 'arkg-BL-' || hash-to-field-DST || info
        F: GF(N), the scalar field
           of the prime order subgroup of crv
        p: N
        m: 1
        L: The L defined in hash-to-crv-suite
        expand_message: The expand_message function
                        defined in hash-to-crv-suite

    pk_tau = pk + tau' * G


BL-Blind-Private-Key(sk, tau, info) -> sk_tau

    tau' = hash_to_field(tau, 1) with the parameters:
        DST: 'arkg-BL-' || hash-to-field-DST || info
        F: GF(N), the scalar field
           of the prime order subgroup of crv.
        p: N
        m: 1
        L: The L defined in hash-to-crv-suite
        expand_message: The expand_message function
                        defined in hash-to-crv-suite

    sk_tau_tmp = sk + tau'
    If sk_tau_tmp = 0, abort with an error.
    sk_tau = sk_tau_tmp
~~~


## Using ECDH as the KEM {#kem-ecdh}

Instantiations of ARKG can use ECDH [RFC6090] as the key encapsulation mechanism `KEM` [Frymann2020]&nbsp;[Wilson].
This section defines a general formula for such instantiations of `KEM`.

This formula has the following parameters:

- `crv`: an elliptic curve valid for use with ECDH [RFC6090].

The `KEM` parameter of ARKG may be instantiated as follows:

- `Elliptic-Curve-Point-to-Octet-String` and `Octet-String-to-Elliptic-Curve-Point`
  are the conversion routines defined in sections 2.3.3 and 2.3.4 of [SEC1].

- `ECDH(pk, sk)` represents the compact output of ECDH [RFC6090]
  using public key (curve point) `pk` and private key (exponent) `sk`.

- `G` is the generator of the prime order subgroup of `crv`.
- `N` is the order of `G`.

~~~pseudocode
Kem-Generate-Keypair() -> (pk, sk)

    Generate (pk, sk) using some procedure defined for crv.


Kem-Encaps(pk, info) -> (k, c)

    (pk', sk') = Kem-Generate-Keypair()

    k = ECDH(pk, sk')
    c = Elliptic-Curve-Point-to-Octet-String(pk')


Kem-Decaps(sk, c, info) -> k

    pk' = Octet-String-to-Elliptic-Curve-Point(c)
    k = ECDH(pk', sk)
~~~


## Using X25519 or X448 as the KEM {#kem-x25519-x448}

Instantiations of ARKG can use X25519 or X448 [RFC7748] as the key encapsulation mechanism `KEM`.
This section defines a general formula for such instantiations of `KEM`.

This formula has the following parameters:

- `DH-Function`: the function X25519 or the function X448 [RFC7748].

The `KEM` parameter of ARKG may be instantiated as follows:

- `Random-Bytes(N)` represents a cryptographically secure,
  uniformly distributed random octet string of length `N`.
- `L` is 32 if `DH-Function` is X25519, or 56 if `DH-Function` is X448.
- `G` is the octet string `h'0900000000000000 0000000000000000 0000000000000000 0000000000000000'`
  if `DH-Function` is X25519,
  or the octet string `h'0500000000000000 0000000000000000 0000000000000000 0000000000000000 0000000000000000 0000000000000000 0000000000000000'`
  if `DH-Function` is X448.

  These are the little-endian encodings of the integers 9 and 5,
  which is the u-coordinate of the generator point of the respective curve group.

~~~pseudocode
Kem-Generate-Keypair() -> (pk, sk)

    sk = Random-Bytes(L)
    pk = DH-Function(sk, G)


Kem-Encaps(pk, info) -> (k, c)

    (pk', sk') = Kem-Generate-Keypair()

    k = DH-Function(sk', pk)
    c = pk'


Kem-Decaps(sk, c, info) -> k

    k = DH-Function(sk, c)
~~~


## Using the same key for both key blinding and KEM {#blinding-kem-same-key}

When an ARKG instance uses the same type of key for both the key blinding and the KEM -
for example, if elliptic curve arithmetic is used for key blinding as described in {{blinding-ec}}
and ECDH is used as the KEM as described in {{kem-ecdh}} [Frymann2020] -
then the two keys MAY be the same key.
Representations of such an ARKG seed MAY allow for omitting the second copy of the constituent key,
but such representations MUST clearly identify that the single constituent key is to be used
both as the key blinding key and the KEM key.


## Using HMAC to augment a KEM with ciphertext integrity {#hmac-kem}

As described in {{arkg-seed-correlation}},
some implementations may require a KEM that guarantees ciphertext integrity,
meaning that a valid KEM ciphertext can be created only with knowledge of the KEM public key
and any domain separation parameters.
Not all KEMs provide this guarantee,
so this section defines a general formula for augmenting any KEM with ciphertext integrity
by prepending a MAC to the KEM ciphertext.

For example, ECDH does not guarantee ciphertext integrity - any elliptic curve point is a valid ECDH ciphertext
and can be successfully decapsulated using any elliptic curve private scalar.

This formula has the following parameters:

- `Hash`: A cryptographic hash function suitable for use in HMAC [RFC2104] and HKDF [RFC5869].
- `Sub-Kem`: An instance of the `KEM` parameter described in {{arkg-params}}.
  This `KEM` instance defines functions `KEM-Generate-Keypair`, `KEM-Encaps` and `KEM-Decaps`
  which are respectively referred to below as `Sub-Kem-Generate-Keypair`, `Sub-Kem-Encaps` and `Sub-Kem-Decaps`.

The `KEM` parameter of ARKG may be instantiated using `Sub-Kem`,
HMAC [RFC2104] and HKDF [RFC5869] as follows:

- `L` is the output length of `Hash` in octets.
- `LEFT(X, n)` is the first `n` bytes of the byte array `X`.
- `DROP_LEFT(X, n)` is the byte array `X` without the first `n` bytes.

We truncate the HMAC output to 128 bits (16 octets)
because as described in {{arkg-seed-correlation}},
ARKG needs ciphertext integrity only to ensure correctness, not for security.
Extendable-output functions used as the `Hash` parameter SHOULD still be instantiated
with an output length appropriate for the desired security level,
in order to not leak information about the `Sub-KEM` shared secret key.
Instantiations of this formula SHOULD prefer `Hash` functions already used in the algorithm suite.

This formula ensures domain separation from the base KEM
by prepending a prefix to the domain separation tag `info` of `Sub-KEM`
and by passing the base KEM shared secret `k'` through HKDF
to produce the final shared secret `k`.

~~~pseudocode

KEM-Generate-Keypair() -> (pk, sk)

    (pk, sk) = Sub-Kem-Generate-Keypair()


KEM-Encaps(pk, info) -> (k, c)

    (k', c') = Sub-Kem-Encaps(pk, 'arkg-KEM-hmac' || info)

    prk = HKDF-Extract with the arguments:
        Hash: Hash
        salt: not set
        IKM: k'

    mk = HKDF-Expand with the arguments:
        Hash: Hash
        PRK: prk
        info: 'arkg-KEM-mac' || info
        L: L
    t = HMAC-Hash-128(K=mk, text=info)

    k = HKDF-Expand with the arguments:
        Hash: Hash
        PRK: prk
        info: 'arkg-KEM-shared' || info
        L: The length of k' in octets.
    c = t || c'


KEM-Decaps(sk, c, info) -> k

    t = LEFT(c, 16)
    c' = DROP_LEFT(c, 16)
    k' = Sub-Kem-Decaps(sk, c', 'arkg-KEM-hmac' || info)

    prk = HKDF-Extract with the arguments:
        Hash: Hash
        salt: not set
        IKM: k'

    mk = HKDF-Expand with the arguments:
        Hash: Hash
        PRK: prk
        info: 'arkg-KEM-mac' || info
        L: L

    t' = HMAC-Hash-128(K=mk, text=info)
    If t = t':
        k = HKDF-Expand with the arguments:
            Hash: Hash
            PRK: prk
            info: 'arkg-KEM-shared' || info
            L: The length of k' in octets.
    Else:
        Abort with an error.
~~~


# Concrete ARKG instantiations

This section defines an initial set of concrete ARKG instantiations.

TODO: IANA registry? COSE/JOSE?


## ARKG-P256ADD-ECDH

The identifier `ARKG-P256ADD-ECDH` represents the following ARKG instance:

- `BL`: Elliptic curve addition as described in {{blinding-ec}} with the parameters:
  - `crv`: The NIST curve `secp256r1` [SEC2].
  - `hash-to-crv-suite`: `P256_XMD:SHA-256_SSWU_RO_` [RFC9380].
  - `hash-to-field-DST`: `'ARKG-P256ADD-ECDH'`.
- `KEM`: ECDH as described in {{kem-ecdh}} with the parameters:
  - `crv`: The NIST curve `secp256r1` [SEC2].


## ARKG-P256ADD-ECDH-HMAC

The identifier `ARKG-P256ADD-ECDH-HMAC` represents the following ARKG instance:

- `BL`: Elliptic curve addition as described in {{blinding-ec}} with the parameters:
  - `crv`: The NIST curve `secp256r1` [SEC2].
  - `hash-to-crv-suite`: `P256_XMD:SHA-256_SSWU_RO_` [RFC9380].
  - `hash-to-field-DST`: `'ARKG-P256ADD-ECDH-HMAC'`.
- `KEM`: A HMAC-augmented KEM as described in {{hmac-kem}} with the parameters:
  - `Hash`: SHA-256 [FIPS 180-4].
  - `Sub-Kem`: ECDH as described in {{kem-ecdh}} with the parameters:
    - `crv`: The NIST curve `secp256r1` [SEC2].


## ARKG-P384ADD-ECDH

The identifier `ARKG-P384ADD-ECDH` represents the following ARKG instance:

- `BL`: Elliptic curve addition as described in {{blinding-ec}} with the parameters:
  - `crv`: The NIST curve `secp384r1` [SEC2].
  - `hash-to-crv-suite`: `P384_XMD:SHA-384_SSWU_RO_` [RFC9380].
  - `hash-to-field-DST`: `'ARKG-P384ADD-ECDH'`.
- `KEM`: ECDH as described in {{kem-ecdh}} with the parameters:
  - `crv`: The NIST curve `secp384r1` [SEC2].


## ARKG-P384ADD-ECDH-HMAC

The identifier `ARKG-P384ADD-ECDH-HMAC` represents the following ARKG instance:

- `BL`: Elliptic curve addition as described in {{blinding-ec}} with the parameters:
  - `crv`: The NIST curve `secp384r1` [SEC2].
  - `hash-to-crv-suite`: `P384_XMD:SHA-384_SSWU_RO_` [RFC9380].
  - `hash-to-field-DST`: `'ARKG-P384ADD-ECDH-HMAC'`.
- `KEM`: A HMAC-augmented KEM as described in {{hmac-kem}} with the parameters:
  - `Hash`: SHA-384 [FIPS 180-4].
  - `Sub-Kem`: ECDH as described in {{kem-ecdh}} with the parameters:
    - `crv`: The NIST curve `secp384r1` [SEC2].


## ARKG-P521ADD-ECDH

The identifier `ARKG-P521ADD-ECDH` represents the following ARKG instance:

- `BL`: Elliptic curve addition as described in {{blinding-ec}} with the parameters:
  - `crv`: The NIST curve `secp521r1` [SEC2].
  - `hash-to-crv-suite`: `P521_XMD:SHA-512_SSWU_RO_` [RFC9380].
  - `hash-to-field-DST`: `'ARKG-P521ADD-ECDH'`.
- `KEM`: ECDH as described in {{kem-ecdh}} with the parameters:
  - `crv`: The NIST curve `secp521r1` [SEC2].
  - `Hash`: SHA-512 [FIPS 180-4].


## ARKG-P521ADD-ECDH-HMAC

The identifier `ARKG-P521ADD-ECDH-HMAC` represents the following ARKG instance:

- `BL`: Elliptic curve addition as described in {{blinding-ec}} with the parameters:
  - `crv`: The NIST curve `secp521r1` [SEC2].
  - `hash-to-crv-suite`: `P521_XMD:SHA-512_SSWU_RO_` [RFC9380].
  - `hash-to-field-DST`: `'ARKG-P521ADD-ECDH-HMAC'`.
- `KEM`: A HMAC-augmented KEM as described in {{hmac-kem}} with the parameters:
  - `Hash`: SHA-512 [FIPS 180-4].
  - `Sub-Kem`: ECDH as described in {{kem-ecdh}} with the parameters:
    - `crv`: The NIST curve `secp521r1` [SEC2].


## ARKG-P256kADD-ECDH

The identifier `ARKG-P256kADD-ECDH` represents the following ARKG instance:

- `BL`: Elliptic curve addition as described in {{blinding-ec}} with the parameters:
  - `crv`: The SECG curve `secp256k1` [SEC2].
  - `hash-to-crv-suite`: `secp256k1_XMD:SHA-256_SSWU_RO_` [RFC9380].
  - `hash-to-field-DST`: `'ARKG-P256kADD-ECDH'`.
- `KEM`: ECDH as described in {{kem-ecdh}} with the parameters:
  - `crv`: The SECG curve `secp256k1` [SEC2].
  - `Hash`: SHA-256 [FIPS 180-4].


## ARKG-P256kADD-ECDH-HMAC

The identifier `ARKG-P256kADD-ECDH-HMAC` represents the following ARKG instance:

- `BL`: Elliptic curve addition as described in {{blinding-ec}} with the parameters:
  - `crv`: The SECG curve `secp256k1` [SEC2].
  - `hash-to-crv-suite`: `secp256k1_XMD:SHA-256_SSWU_RO_` [RFC9380].
  - `hash-to-field-DST`: `'ARKG-P256kADD-ECDH-HMAC'`.
- `KEM`: A HMAC-augmented KEM as described in {{hmac-kem}} with the parameters:
  - `Hash`: SHA-256 [FIPS 180-4].
  - `Sub-Kem`: ECDH as described in {{kem-ecdh}} with the parameters:
    - `crv`: The SECG curve `secp256k1` [SEC2].


## ARKG-curve25519ADD-X25519

The identifier `ARKG-curve25519ADD-X25519` represents the following ARKG instance:

- `BL`: Elliptic curve addition as described in {{blinding-ec}} with the parameters:
  - `crv`: The curve `curve25519` [RFC7748].
  - `hash-to-crv-suite`: `curve25519_XMD:SHA-512_ELL2_RO_` [RFC9380].
  - `hash-to-field-DST`: `'ARKG-curve25519ADD-X25519'`.

  WARNING: Some algorithms on curve25519, including X25519 [RFC7748],
  construct private key scalars within a particular range
  to enable optimizations and constant-time guarantees.
  This `BL` scheme does not guarantee that blinded private scalars remain in that range,
  so implementations using this ARKG instance MUST NOT rely on such a guarantee.

  Note: Input and output keys of this `BL` scheme are curve scalars and curve points.
  Some algorithms on curve25519, including X25519 [RFC7748],
  define the private key input as a random octet string and applies some preprocessing to it
  before interpreting the result as a private key scalar,
  and define public keys as a particular octet string encoding of a curve point.
  This `BL` scheme is not compatible with such preprocessing
  since it breaks the relationship between the blinded private key and the blinded public key.
  Implementations using this ARKG instance MUST apply `BL-Blind-Private-Key`
  to the interpreted private key scalar, not the random private key octet string,
  and implementations of `BL-Blind-Public-Key` MUST interpret the public key input as a curve point,
  not an opaque octet string.

- `KEM`: X25519 as described in {{kem-x25519-x448}} with the parameters:
  - `DH-Function`: X25519 [RFC7748].


## ARKG-curve25519ADD-X25519-HMAC

The identifier `ARKG-curve25519ADD-X25519-HMAC` represents the following ARKG instance:

- `BL`: Elliptic curve addition as described in {{blinding-ec}} with the parameters:
  - `crv`: The curve `curve25519` [RFC7748].
  - `hash-to-crv-suite`: `curve25519_XMD:SHA-512_ELL2_RO_` [RFC9380].
  - `hash-to-field-DST`: `'ARKG-curve25519ADD-X25519-HMAC'`.

  WARNING: Some algorithms on curve25519, including X25519 [RFC7748],
  construct private key scalars within a particular range
  to enable optimizations and constant-time guarantees.
  This `BL` scheme does not guarantee that blinded private scalars remain in that range,
  so implementations using this ARKG instance MUST NOT rely on such a guarantee.

  Note: Input and output keys of this `BL` scheme are curve scalars and curve points.
  Some algorithms on curve25519, including X25519 [RFC7748],
  define the private key input as a random octet string and applies some preprocessing to it
  before interpreting the result as a private key scalar,
  and define public keys as a particular octet string encoding of a curve point.
  This `BL` scheme is not compatible with such preprocessing
  since it breaks the relationship between the blinded private key and the blinded public key.
  Implementations using this ARKG instance MUST apply `BL-Blind-Private-Key`
  to the interpreted private key scalar, not the random private key octet string,
  and implementations of `BL-Blind-Public-Key` MUST interpret the public key input as a curve point,
  not an opaque octet string.

- `KEM`: A HMAC-augmented KEM as described in {{hmac-kem}} with the parameters:
  - `Hash`: SHA-512 [FIPS 180-4].
  - `Sub-Kem`: X25519 as described in {{kem-x25519-x448}} with the parameters:
    - `DH-Function`: X25519 [RFC7748].


## ARKG-curve448ADD-X448

The identifier `ARKG-curve448ADD-X448` represents the following ARKG instance:

- `BL`: Elliptic curve addition as described in {{blinding-ec}} with the parameters:
  - `crv`: The curve `curve448` [RFC7748].
  - `hash-to-crv-suite`: `curve448_XOF:SHAKE256_ELL2_RO_` [RFC9380].
  - `hash-to-field-DST`: `'ARKG-curve448ADD-X448'`.

  WARNING: Some algorithms on curve25519, including X448 [RFC7748],
  construct private key scalars within a particular range
  to enable optimizations and constant-time guarantees.
  This `BL` scheme does not guarantee that blinded private scalars remain in that range,
  so implementations using this ARKG instance MUST NOT rely on such a guarantee.

  Note: Input and output keys of this `BL` scheme are curve scalars and curve points.
  Some algorithms on curve25519, including X448 [RFC7748],
  define the private key input as a random octet string and applies some preprocessing to it
  before interpreting the result as a private key scalar,
  and define public keys as a particular octet string encoding of a curve point.
  This `BL` scheme is not compatible with such preprocessing
  since it breaks the relationship between the blinded private key and the blinded public key.
  Implementations using this ARKG instance MUST apply `BL-Blind-Private-Key`
  to the interpreted private key scalar, not the random private key octet string,
  and implementations of `BL-Blind-Public-Key` MUST interpret the public key input as a curve point,
  not an opaque octet string.

- `KEM`: X448 as described in {{kem-x25519-x448}} with the parameters:
  - `DH-Function`: X448 [RFC7748].


## ARKG-curve448ADD-X448-HMAC

The identifier `ARKG-curve448ADD-X448-HMAC` represents the following ARKG instance:

- `BL`: Elliptic curve addition as described in {{blinding-ec}} with the parameters:
  - `crv`: The curve `curve448` [RFC7748].
  - `hash-to-crv-suite`: `curve448_XOF:SHAKE256_ELL2_RO_` [RFC9380].
  - `hash-to-field-DST`: `'ARKG-curve448ADD-X448-HMAC'`.

  WARNING: Some algorithms on curve25519, including X448 [RFC7748],
  construct private key scalars within a particular range
  to enable optimizations and constant-time guarantees.
  This `BL` scheme does not guarantee that blinded private scalars remain in that range,
  so implementations using this ARKG instance MUST NOT rely on such a guarantee.

  Note: Input and output keys of this `BL` scheme are curve scalars and curve points.
  Some algorithms on curve25519, including X448 [RFC7748],
  define the private key input as a random octet string and applies some preprocessing to it
  before interpreting the result as a private key scalar,
  and define public keys as a particular octet string encoding of a curve point.
  This `BL` scheme is not compatible with such preprocessing
  since it breaks the relationship between the blinded private key and the blinded public key.
  Implementations using this ARKG instance MUST apply `BL-Blind-Private-Key`
  to the interpreted private key scalar, not the random private key octet string,
  and implementations of `BL-Blind-Public-Key` MUST interpret the public key input as a curve point,
  not an opaque octet string.

- `KEM`: A HMAC-augmented KEM as described in {{hmac-kem}} with the parameters:
  - `Hash`: SHAKE256 [FIPS 202] with output length 64 octets.
  - `Sub-Kem`: X448 as described in {{kem-x25519-x448}} with the parameters:
    - `DH-Function`: X448 [RFC7748].


## ARKG-edwards25519ADD-X25519

The identifier `ARKG-edwards25519ADD-X25519` represents the following ARKG instance:

- `BL`: Elliptic curve addition as described in {{blinding-ec}} with the parameters:
  - `crv`: The curve `edwards25519` [RFC7748].
  - `hash-to-crv-suite`: `edwards25519_XMD:SHA-512_ELL2_RO_` [RFC9380].
  - `hash-to-field-DST`: `'ARKG-edwards25519ADD-X25519'`.

  WARNING: Some algorithms on edwards25519, including EdDSA [RFC8032],
  construct private key scalars within a particular range
  to enable optimizations and constant-time guarantees.
  This `BL` scheme does not guarantee that blinded private scalars remain in that range,
  so implementations using this ARKG instance MUST NOT rely on such a guarantee.

  Note: Input and output keys of this `BL` scheme are curve scalars and curve points.
  Some algorithms on edwards25519, including EdDSA [RFC8032],
  define the private key input as a random octet string and applies some preprocessing to it
  before interpreting the result as a private key scalar,
  and define public keys as a particular octet string encoding of a curve point.
  This `BL` scheme is not compatible with such preprocessing
  since it breaks the relationship between the blinded private key and the blinded public key.
  Implementations using this ARKG instance MUST apply `BL-Blind-Private-Key`
  to the interpreted private key scalar, not the random private key octet string,
  and implementations of `BL-Blind-Public-Key` MUST interpret the public key input as a curve point,
  not an opaque octet string.

- `KEM`: X25519 as described in {{kem-x25519-x448}} with the parameters:
  - `DH-Function`: X25519 [RFC7748].


## ARKG-edwards25519ADD-X25519-HMAC

The identifier `ARKG-edwards25519ADD-X25519-HMAC` represents the following ARKG instance:

- `BL`: Elliptic curve addition as described in {{blinding-ec}} with the parameters:
  - `crv`: The curve `edwards25519` [RFC7748].
  - `hash-to-crv-suite`: `edwards25519_XMD:SHA-512_ELL2_RO_` [RFC9380].
  - `hash-to-field-DST`: `'ARKG-edwards25519ADD-X25519-HMAC'`.

  WARNING: Some algorithms on edwards25519, including EdDSA [RFC8032],
  construct private key scalars within a particular range
  to enable optimizations and constant-time guarantees.
  This `BL` scheme does not guarantee that blinded private scalars remain in that range,
  so implementations using this ARKG instance MUST NOT rely on such a guarantee.

  Note: Input and output keys of this `BL` scheme are curve scalars and curve points.
  Some algorithms on edwards25519, including EdDSA [RFC8032],
  define the private key input as a random octet string and applies some preprocessing to it
  before interpreting the result as a private key scalar,
  and define public keys as a particular octet string encoding of a curve point.
  This `BL` scheme is not compatible with such preprocessing
  since it breaks the relationship between the blinded private key and the blinded public key.
  Implementations using this ARKG instance MUST apply `BL-Blind-Private-Key`
  to the interpreted private key scalar, not the random private key octet string,
  and implementations of `BL-Blind-Public-Key` MUST interpret the public key input as a curve point,
  not an opaque octet string.

- `KEM`: A HMAC-augmented KEM as described in {{hmac-kem}} with the parameters:
  - `Hash`: SHA-512 [FIPS 180-4].
  - `Sub-Kem`: X25519 as described in {{kem-x25519-x448}} with the parameters:
    - `DH-Function`: X25519 [RFC7748].


## ARKG-edwards448ADD-X448

The identifier `ARKG-edwards448ADD-X448` represents the following ARKG instance:

- `BL`: Elliptic curve addition as described in {{blinding-ec}} with the parameters:
  - `crv`: The curve `edwards448` [RFC7748].
  - `hash-to-crv-suite`: `edwards448_XOF:SHAKE256_ELL2_RO_` [RFC9380].
  - `hash-to-field-DST`: `'ARKG-edwards448ADD-X448'`.

  WARNING: Some algorithms on edwards25519, including EdDSA [RFC8032],
  construct private key scalars within a particular range
  to enable optimizations and constant-time guarantees.
  This `BL` scheme does not guarantee that blinded private scalars remain in that range,
  so implementations using this ARKG instance MUST NOT rely on such a guarantee.

  Note: Input and output keys of this `BL` scheme are curve scalars and curve points.
  Some algorithms on edwards25519, including EdDSA [RFC8032],
  define the private key input as a random octet string and applies some preprocessing to it
  before interpreting the result as a private key scalar,
  and define public keys as a particular octet string encoding of a curve point.
  This `BL` scheme is not compatible with such preprocessing
  since it breaks the relationship between the blinded private key and the blinded public key.
  Implementations using this ARKG instance MUST apply `BL-Blind-Private-Key`
  to the interpreted private key scalar, not the random private key octet string,
  and implementations of `BL-Blind-Public-Key` MUST interpret the public key input as a curve point,
  not an opaque octet string.

- `KEM`: X448 as described in {{kem-x25519-x448}} with the parameters:
  - `DH-Function`: X448 [RFC7748].


## ARKG-edwards448ADD-X448-HMAC

The identifier `ARKG-edwards448ADD-X448-HMAC` represents the following ARKG instance:

- `BL`: Elliptic curve addition as described in {{blinding-ec}} with the parameters:
  - `crv`: The curve `edwards448` [RFC7748].
  - `hash-to-crv-suite`: `edwards448_XOF:SHAKE256_ELL2_RO_` [RFC9380].
  - `hash-to-field-DST`: `'ARKG-edwards448ADD-X448-HMAC'`.

  WARNING: Some algorithms on edwards25519, including EdDSA [RFC8032],
  construct private key scalars within a particular range
  to enable optimizations and constant-time guarantees.
  This `BL` scheme does not guarantee that blinded private scalars remain in that range,
  so implementations using this ARKG instance MUST NOT rely on such a guarantee.

  Note: Input and output keys of this `BL` scheme are curve scalars and curve points.
  Some algorithms on edwards25519, including EdDSA [RFC8032],
  define the private key input as a random octet string and applies some preprocessing to it
  before interpreting the result as a private key scalar,
  and define public keys as a particular octet string encoding of a curve point.
  This `BL` scheme is not compatible with such preprocessing
  since it breaks the relationship between the blinded private key and the blinded public key.
  Implementations using this ARKG instance MUST apply `BL-Blind-Private-Key`
  to the interpreted private key scalar, not the random private key octet string,
  and implementations of `BL-Blind-Public-Key` MUST interpret the public key input as a curve point,
  not an opaque octet string.

- `KEM`: A HMAC-augmented KEM as described in {{hmac-kem}} with the parameters:
  - `Hash`: SHAKE256 [FIPS 202] with output length 64 octets.
  - `Sub-Kem`: X448 as described in {{kem-x25519-x448}} with the parameters:
    - `DH-Function`: X448 [RFC7748].


# COSE bindings

TODO?: Define COSE representations for interoperability:
- ARKG public seed (for interoperability between different implementers of `ARKG-Generate-Seed` and `ARKG-Derive-Public-Key`)
- ARKG key handle (for interoperability between different implementers of `ARKG-Derive-Public-Key` and `ARKG-Derive-Private-Key`)


# Implementation Considerations {#Implementation}

## Identifying the ARKG seed {#arkg-seed-id}

In some use cases there might exist multiple ARKG seed pairs or multiple candidate key handles in the same context,
so the subordinate party must somehow communicate to the delegate party
which key handle belongs to which ARKG seed.

For example, applications using the W3C Web Authentication API [WebAuthn]
do not know beforehand which authenticators are connected and available.
Instead, authentication requests may include references to several eligible authenticators,
and the one to use is chosen opportunistically by the WebAuthn client depending on which are available at the time.
Consider using ARKG in such a scenario to sign some data with a derived private key:
if the authenticator - the delegating party - chooses the wrong combination of private seed and key handle,
this might cause the `ARKG-Derive-Private-Key` procedure to silently derive the wrong key instead of returning an explicit error,
which would in turn lead to an invalid signature.
This might not be detected until a third party attempts to verify the signature,
at which point it may be difficult or impossible to diagnose the root cause of the invalid signature and present actionable user feedback.

A simple solution for this is to have the delegating party emit an opaque identifier for the ARKG seed pair
along with the result of `ARKG-Generate-Seed`,
and have the subordinate party communicate that identifier along with the key handle output of `ARKG-Derive-Public-Key`.
This way the delegating party knows which ARKG private seed to use with which key handle
to compute the correct result in `ARKG-Derive-Private-Key`,
and can ignore any key handles that belong to a different delegating party.

However, this solution may be unsuitable for some implementations due to privacy implications.
This is discussed further in {{arkg-seed-correlation}}.


# Security Considerations {#Security}

## Using a MAC {#security-mac}

{{hmac-kem}} specifies a formula for adding a MAC to ARKG key handles.
The ARKG construction by Wilson [Wilson] omits this MAC and instead encodes application context in the PRF labels,
arguing that this leads to invalid keys/signatures in cases that would have a bad MAC.
For reasons described in {{arkg-seed-correlation}},
we choose for some ARKG instantiations to keep the MAC from the construction by Frymann et al. [Frymann2020].
This is not necessary in case the ARKG seed can be identified by other means as described in {{arkg-seed-id}}
or if the chosen KEM already guarantees ciphertext integrity as defined in {{arkg-seed-correlation}}.

It is straightforward to see that adding the MAC to the construction by Wilson
does not weaken the security properties defined by Frymann et al. [Frymann2020]:
the construction by Frymann et al. can be reduced to the ARKG construction in this document
by instantiating `KEM` as group exponentiation
and instantiating `BL` as group multiplication to blind public keys and modular integer addition to blind private keys.
The use of HMAC and HKDF in {{hmac-kem}} corresponds to the MAC and KDF parameters in [Frymann2020],
where KDF<sub>1</sub>(_k_) = KDF(_k_, _l_<sub>1</sub>) and KDF<sub>2</sub>(_k_) = KDF(_k_, _l_<sub>2</sub>)
with fixed labels _l_<sub>1</sub> and _l_<sub>2</sub>.
Hence if one can break PK-unlinkability or SK-security of the ARKG construction in this document,
one can also break the same property of the construction by Frymann et al.


# Privacy Considerations {#Privacy}

## ARKG seed correlatability {#arkg-seed-correlation}

{{arkg-seed-id}} discusses why some implementations may require a way to identify
which ARKG key handle belongs to which ARKG seed.
However, a static identifier could be an unacceptable correlation handle
in some use cases where the key handle may be communicated through an untrusted channel.

For example, the original ARKG proposal [Frymann2020] studied a proposed extension to W3C Web Authentication (WebAuthn)
where the delegating and subordinate parties are WebAuthn authenticators
and the key handle is communicated through a WebAuthn Relying Party,
and that Relying Party must be prevented from tracking users by correlating ARKG key handles.

The same paper solves the correlation issue by attaching a MAC to the key handle
instead of attaching an identifier for the ARKG seed.
The MAC tag is computed from the KEM shared key,
and so requires knowledge of the ARKG public seed and any domain separation parameters to compute.
This way the delegating party can ensure correctness in `ARKG-Derive-Private-Key`
by rejecting any key handle with an invalid MAC,
as it was most likely computed for a different ARKG seed.

We choose here to model this capability as "KEM ciphertext integrity",
meaning that knowledge of the KEM public key and any domain separation parameters
is required in order to create any KEM ciphertext that can be successfully decapsulated by the corresponding KEM private key.
{{hmac-kem}} specifies a general formula for augmenting any KEM with a MAC to guarantee ciphertext integrity.


TODO


# IANA Considerations {#IANA}

TODO


## Implementation Status

TODO


--- back

# Acknowledgements

ARKG was first proposed under this name by Frymann et al. [Frymann2020],
who analyzed a proposed extension to W3C Web Authentication by Lundberg and Nilsson [WebAuthn-Recovery],
which was in turn inspired by a similar construction by Wuille [BIP32] used to create privacy-preserving Bitcoin addresses.
Frymann et al. [Frymann2020] generalized the constructions by Lundberg, Nilsson and Wuille
from elliptic curves to any discrete logarithm (DL) problem,
and also proved the security of arbitrary asymmetric protocols composed with ARKG.
Further generalizations to include quantum-resistant instantiations
were developed independently by Clermont [Clermont], Frymann et al. [Frymann2023] and Wilson [Wilson].

This document adopts the construction proposed by Wilson [Wilson],
modified by the inclusion of a MAC in the key handles as done in the original construction by Frymann et al. [Frymann2020].

The authors would like to thank all of these authors for their research and development work that led to the creation of this document.


# Test Vectors

TODO


# Document History

-00
  Initial Version

-01
  Editorial Fixes to formatting and references.
