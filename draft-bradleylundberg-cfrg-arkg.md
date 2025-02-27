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
- fullname: Dain Nilsson
  organization: Yubico

- fullname: Peter Altmann
  organization: Agency for Digital Government
  country: SE

normative:
  I-D.jose-fully-spec-algs: I-D.draft-ietf-jose-fully-specified-algorithms
  I-D.lundberg-cose-2p-algs: I-D.draft-lundberg-cose-two-party-signing-algs
  IANA.cose:
  RFC2104:
  RFC4949:
  RFC5869:
  RFC6090:
  RFC7748:
  RFC8032:
  RFC8610:
  RFC8812:
  RFC9052:
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
      org: "Technische Universität Darmstadt"
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
  Shoup:
    author:
    - name: Victor Shoup
      org: IBM Zurich Research Lab
    title: A Proposal for an ISO Standard for Public Key Encryption (version 2.0)
    date: 2001
    target: https://www.shoup.net/papers/iso-2.pdf
  Wilson:
    author:
    - name: Spencer MacLaren Wilson
      org: University of Waterloo,
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

  - Function `BL-Blind-Public-Key(pk, tau, info) -> pk_tau`: Deterministically compute a blinded public key.

    Input consists of a blinding public key `pk`,
    a blinding factor `tau`
    and a domain separation parameter `info`.

    Output consists of the blinded public key `pk_tau`.

  - Function `BL-Blind-Private-Key(sk, tau, info) -> sk_tau`: Deterministically compute a blinded private key.

    Input consists of a blinding private key `sk`,
    a blinding factor `tau`
    and a domain separation parameter `info`.

    Output consists of the blinded private key `sk_tau`.

  `tau` and `info` are an opaque octet strings of arbitrary length.
  The representations of `pk` and `pk_tau` are defined by the protocol that invokes ARKG.
  The representations of `sk` and `sk_tau` are an undefined implementation detail.

  See [Wilson] for definitions of security properties required of the key blinding scheme `BL`.

- `KEM`: A key encapsulation mechanism [Shoup], consisting of the functions:
  - `KEM-Generate-Keypair() -> (pk, sk)`: Generate a key encapsulation key pair.

    No input.

    Output consists of public key `pk` and private key `sk`.

  - `KEM-Encaps(pk, info) -> (k, c)`: Generate a key encapsulation.

    Input consists of an encapsulation public key `pk`
    and a domain separation parameter `info`.

    Output consists of a shared secret `k` and an encapsulation ciphertext `c`.

  - `KEM-Decaps(sk, c, info) -> k`: Decapsulate a shared secret.

    Input consists of encapsulation private key `sk`, encapsulation ciphertext `c`
    and a domain separation parameter `info`.

    Output consists of the shared secret `k` on success, or an error otherwise.

  `k`, `c` and `info` are opaque octet strings of arbitrary length.
  The representation of `pk` is defined by the protocol that invokes ARKG.
  The representation of `sk` is an undefined implementation detail.

  The KEM MUST guarantee integrity of the ciphertext,
  meaning that knowledge of the public key `pk` and the domain separation parameter `info`
  is required in order to create any ciphertext `c` that can be successfully decapsulated by the corresponding private key `sk`.
  {{hmac-kem}} describes a general formula for how any KEM can be adapted to include this guarantee.
  {{design-rationale-mac}} discusses the reasons for this requirement.

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

    info_kem = 'ARKG-Derive-Key-KEM.' || info
    info_bl  = 'ARKG-Derive-Key-BL.'  || info

    (tau, c) = KEM-Encaps(pk_kem, info_kem)
    pk' = BL-Blind-Public-Key(pk_bl, tau, info_bl)

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

    info_kem = 'ARKG-Derive-Key-KEM.' || info
    info_bl  = 'ARKG-Derive-Key-BL.'  || info

    tau = KEM-Decaps(sk_kem, kh, info_kem)
    If decapsulation failed:
        Abort with an error.

    sk' = BL-Blind-Private-Key(sk_bl, tau, info_bl)
~~~

Errors in this procedure are typically unrecoverable.
For example, `KEM-Decaps` may fail to decapsulate the KEM ciphertext `kh` if it fails an integrity check.
ARKG instantiations SHOULD be chosen in a way that such errors are impossible
if `kh` was generated by an honest and correct implementation of `ARKG-Derive-Public-Key`.
Incorrect or malicious implementations of `ARKG-Derive-Public-Key` do not degrade the security
of a correct and honest implementation of `ARKG-Derive-Private-Key`.
See also {{design-rationale-mac}}.


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
- `DST_ext`: A domain separation tag.

Then the `BL` parameter of ARKG may be instantiated as follows:

- `G` is the generator of the prime order subgroup of `crv`.
- `N` is the order of `G`.
- The function `hash_to_field` is defined in {{Section 5 of RFC9380}}.

~~~pseudocode
BL-Generate-Keypair() -> (pk, sk)

    Generate (pk, sk) using some procedure defined for the curve crv.


BL-Blind-Public-Key(pk, tau, info) -> pk_tau

    tau' = hash_to_field(tau, 1) with the parameters:
        DST: 'ARKG-BL-EC.' || DST_ext || info
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
        DST: 'ARKG-BL-EC.' || DST_ext || info
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


## Using HMAC to adapt a KEM without ciphertext integrity {#hmac-kem}

Not all key encapsulation mechanisms guarantee ciphertext integrity,
meaning that a valid KEM ciphertext can be created only with knowledge of the KEM public key.
This section defines a general formula for adapting any KEM to guarantee ciphertext integrity
by prepending a MAC to the KEM ciphertext.

For example, ECDH does not guarantee ciphertext integrity - any elliptic curve point is a valid ECDH ciphertext
and can be successfully decapsulated using any elliptic curve private scalar.

This formula has the following parameters:

- `Hash`: A cryptographic hash function.
- `DST_ext`: A domain separation parameter.
- `Sub-Kem`: A key encapsulation mechanism as described for the `KEM` parameter in {{arkg-params}},
  except `Sub-Kem` MAY ignore the `info` parameter and MAY not guarantee ciphertext integrity.
  `Sub-Kem` defines the functions `Sub-Kem-Generate-Keypair`, `Sub-Kem-Encaps` and `Sub-Kem-Decaps`.

The `KEM` parameter of ARKG may be instantiated using `Sub-Kem`,
HMAC [RFC2104] and HKDF [RFC5869] as follows:

- `L` is the output length of `Hash` in octets.
- `LEFT(X, n)` is the first `n` bytes of the byte array `X`.
- `DROP_LEFT(X, n)` is the byte array `X` without the first `n` bytes.

We truncate the HMAC output to 128 bits (16 octets)
because as described in {{design-rationale-mac}},
ARKG needs ciphertext integrity only to ensure correctness, not for security.
Extendable-output functions used as the `Hash` parameter SHOULD still be instantiated
with an output length appropriate for the desired security level,
in order to not leak information about the `Sub-KEM` shared secret key.

~~~pseudocode

KEM-Generate-Keypair() -> (pk, sk)

    (pk, sk) = Sub-Kem-Generate-Keypair()


KEM-Encaps(pk, info) -> (k, c)

    info_sub = 'ARKG-KEM-HMAC.' || DST_ext || info
    (k', c') = Sub-Kem-Encaps(pk, info_sub)

    prk = HKDF-Extract with the arguments:
        Hash: Hash
        salt: not set
        IKM: k'

    mk = HKDF-Expand with the arguments:
        Hash: Hash
        PRK: prk
        info: 'ARKG-KEM-HMAC-mac.' || DST_ext || info
        L: L
    t = HMAC-Hash-128(K=mk, text=c')

    k = HKDF-Expand with the arguments:
        Hash: Hash
        PRK: prk
        info: 'ARKG-KEM-HMAC-shared.' || DST_ext || info
        L: The length of k' in octets.
    c = t || c'


KEM-Decaps(sk, c, info) -> k

    t = LEFT(c, 16)
    c' = DROP_LEFT(c, 16)
    info_sub = 'ARKG-KEM-HMAC.' || DST_ext || info
    k' = Sub-Kem-Decaps(sk, c', info_sub)

    prk = HKDF-Extract with the arguments:
        Hash: Hash
        salt: not set
        IKM: k'

    mk = HKDF-Expand with the arguments:
        Hash: Hash
        PRK: prk
        info: 'ARKG-KEM-HMAC-mac.' || DST_ext || info
        L: L

    t' = HMAC-Hash-128(K=mk, text=c')
    If t = t':
        k = HKDF-Expand with the arguments:
            Hash: Hash
            PRK: prk
            info: 'ARKG-KEM-HMAC-shared.' || DST_ext || info
            L: The length of k' in octets.
    Else:
        Abort with an error.
~~~


## Using ECDH as the KEM {#kem-ecdh}

Instantiations of ARKG can use ECDH [RFC6090] as the key encapsulation mechanism `KEM` [Frymann2020]&nbsp;[Wilson].
This section defines a general formula for such instantiations of `KEM`.

This formula has the following parameters:

- `crv`: an elliptic curve valid for use with ECDH [RFC6090].
- `Hash`: A cryptographic hash function.
- `DST_ext`: A domain separation parameter.

The `KEM` parameter of ARKG may be instantiated as described in section {{hmac-kem}} with the parameters:

- `Hash`: `Hash`.
- `DST_ext`: `'ARKG-ECDH.' || DST_ext`.
- `Sub-Kem`: The functions `Sub-Kem-Generate-Keypair`, `Sub-Kem-Encaps` and `Sub-Kem-Decaps` defined as follows:

  - `Elliptic-Curve-Point-to-Octet-String` and `Octet-String-to-Elliptic-Curve-Point`
    are the conversion routines defined in sections 2.3.3 and 2.3.4 of [SEC1],
    without point compression.

  - `ECDH(pk, sk)` represents the compact output of ECDH [RFC6090]
    using public key (curve point) `pk` and private key (exponent) `sk`.

  - `G` is the generator of the prime order subgroup of `crv`.
  - `N` is the order of `G`.

  ~~~pseudocode
  Sub-Kem-Generate-Keypair() -> (pk, sk)

      Generate (pk, sk) using some procedure defined for crv.


  Sub-Kem-Encaps(pk, info) -> (k, c)

      (pk', sk') = Sub-Kem-Generate-Keypair()

      k = ECDH(pk, sk')
      c = Elliptic-Curve-Point-to-Octet-String(pk')


  Sub-Kem-Decaps(sk, c, info) -> k

      pk' = Octet-String-to-Elliptic-Curve-Point(c)
      k = ECDH(pk', sk)
  ~~~


## Using X25519 or X448 as the KEM {#kem-x25519-x448}

Instantiations of ARKG can use X25519 or X448 [RFC7748] as the key encapsulation mechanism `KEM`.
This section defines a general formula for such instantiations of `KEM`.

This formula has the following parameters:

- `DH-Function`: the function X25519 or the function X448 [RFC7748].
- `DST_ext`: A domain separation parameter.

The `KEM` parameter of ARKG may be instantiated as described in section {{hmac-kem}} with the parameters:

- `Hash`: SHA-512 [FIPS 180-4] if `DH-Function` is X25519,
  or SHAKE256 [FIPS 202] with output length 64 octets if `DH-Function` is X448.
- `DST_ext`: `'ARKG-ECDHX.' || DST_ext`.
- `Sub-Kem`: The functions `Sub-Kem-Generate-Keypair`, `Sub-Kem-Encaps` and `Sub-Kem-Decaps` defined as follows:

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
  Sub-Kem-Generate-Keypair() -> (pk, sk)

      sk = Random-Bytes(L)
      pk = DH-Function(sk, G)


  Sub-Kem-Encaps(pk, info) -> (k, c)

      (pk', sk') = Sub-Kem-Generate-Keypair()

      k = DH-Function(sk', pk)
      c = pk'


  Sub-Kem-Decaps(sk, c, info) -> k

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


# Concrete ARKG instantiations

This section defines an initial set of concrete ARKG instantiations.

TODO: IANA registry? COSE/JOSE?


## ARKG-P256ADD-ECDH {#ARKG-P256ADD-ECDH}

The identifier `ARKG-P256ADD-ECDH` represents the following ARKG instance:

- `BL`: Elliptic curve addition as described in {{blinding-ec}} with the parameters:
  - `crv`: The NIST curve `secp256r1` [SEC2].
  - `hash-to-crv-suite`: `P256_XMD:SHA-256_SSWU_RO_` [RFC9380].
  - `DST_ext`: `'ARKG-P256ADD-ECDH'`.
- `KEM`: ECDH as described in {{kem-ecdh}} with the parameters:
  - `crv`: The NIST curve `secp256r1` [SEC2].
  - `Hash`: SHA-256 [FIPS 180-4].
  - `DST_ext`: `'ARKG-P256ADD-ECDH'`.


## ARKG-P384ADD-ECDH {#ARKG-P384ADD-ECDH}

The identifier `ARKG-P384ADD-ECDH` represents the following ARKG instance:

- `BL`: Elliptic curve addition as described in {{blinding-ec}} with the parameters:
  - `crv`: The NIST curve `secp384r1` [SEC2].
  - `hash-to-crv-suite`: `P384_XMD:SHA-384_SSWU_RO_` [RFC9380].
  - `DST_ext`: `'ARKG-P384ADD-ECDH'`.
- `KEM`: ECDH as described in {{kem-ecdh}} with the parameters:
  - `crv`: The NIST curve `secp384r1` [SEC2].
  - `Hash`: SHA-384 [FIPS 180-4].
  - `DST_ext`: `'ARKG-P384ADD-ECDH'`.


## ARKG-P521ADD-ECDH {#ARKG-P521ADD-ECDH}

The identifier `ARKG-P521ADD-ECDH` represents the following ARKG instance:

- `BL`: Elliptic curve addition as described in {{blinding-ec}} with the parameters:
  - `crv`: The NIST curve `secp521r1` [SEC2].
  - `hash-to-crv-suite`: `P521_XMD:SHA-512_SSWU_RO_` [RFC9380].
  - `DST_ext`: `'ARKG-P521ADD-ECDH'`.
- `KEM`: ECDH as described in {{kem-ecdh}} with the parameters:
  - `crv`: The NIST curve `secp521r1` [SEC2].
  - `Hash`: SHA-512 [FIPS 180-4].
  - `DST_ext`: `'ARKG-P521ADD-ECDH'`.


## ARKG-P256kADD-ECDH {#ARKG-P256kADD-ECDH}

The identifier `ARKG-P256kADD-ECDH` represents the following ARKG instance:

- `BL`: Elliptic curve addition as described in {{blinding-ec}} with the parameters:
  - `crv`: The SECG curve `secp256k1` [SEC2].
  - `hash-to-crv-suite`: `secp256k1_XMD:SHA-256_SSWU_RO_` [RFC9380].
  - `DST_ext`: `'ARKG-P256kADD-ECDH'`.
- `KEM`: ECDH as described in {{kem-ecdh}} with the parameters:
  - `crv`: The SECG curve `secp256k1` [SEC2].
  - `Hash`: SHA-256 [FIPS 180-4].
  - `DST_ext`: `'ARKG-P256kADD-ECDH'`.


## ARKG-curve25519ADD-X25519 {#ARKG-curve25519ADD-X25519}

The identifier `ARKG-curve25519ADD-X25519` represents the following ARKG instance:

- `BL`: Elliptic curve addition as described in {{blinding-ec}} with the parameters:
  - `crv`: The curve `curve25519` [RFC7748].
  - `hash-to-crv-suite`: `curve25519_XMD:SHA-512_ELL2_RO_` [RFC9380].
  - `DST_ext`: `'ARKG-curve25519ADD-X25519'`.

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
  - `DST_ext`: `'ARKG-curve25519ADD-X25519'`.


## ARKG-curve448ADD-X448 {#ARKG-curve448ADD-X448}

The identifier `ARKG-curve448ADD-X448` represents the following ARKG instance:

- `BL`: Elliptic curve addition as described in {{blinding-ec}} with the parameters:
  - `crv`: The curve `curve448` [RFC7748].
  - `hash-to-crv-suite`: `curve448_XOF:SHAKE256_ELL2_RO_` [RFC9380].
  - `DST_ext`: `'ARKG-curve448ADD-X448'`.

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
  - `DST_ext`: `'ARKG-curve448ADD-X448'`.


## ARKG-edwards25519ADD-X25519 {#ARKG-edwards25519ADD-X25519}

The identifier `ARKG-edwards25519ADD-X25519` represents the following ARKG instance:

- `BL`: Elliptic curve addition as described in {{blinding-ec}} with the parameters:
  - `crv`: The curve `edwards25519` [RFC7748].
  - `hash-to-crv-suite`: `edwards25519_XMD:SHA-512_ELL2_RO_` [RFC9380].
  - `DST_ext`: `'ARKG-edwards25519ADD-X25519'`.

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
  - `DST_ext`: `'ARKG-edwards25519ADD-X25519'`.


## ARKG-edwards448ADD-X448 {#ARKG-edwards448ADD-X448}

The identifier `ARKG-edwards448ADD-X448` represents the following ARKG instance:

- `BL`: Elliptic curve addition as described in {{blinding-ec}} with the parameters:
  - `crv`: The curve `edwards448` [RFC7748].
  - `hash-to-crv-suite`: `edwards448_XOF:SHAKE256_ELL2_RO_` [RFC9380].
  - `DST_ext`: `'ARKG-edwards448ADD-X448'`.

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
  - `DST_ext`: `'ARKG-edwards448ADD-X448'`.


# COSE bindings {#cose}

This section proposes additions to COSE [RFC9052] to support ARKG use cases.
These consist of new key type definitions to represent ARKG public seeds
and references [I-D.lundberg-cose-2p-algs] to private keys derived using ARKG.


## COSE key type: ARKG public seed {#cose-arkg-pub-seed}

An ARKG public seed is represented as a COSE_Key structure [RFC9052]
with `kty` value TBD (placeholder value -65537).
This key type defines key type parameters -1 and -2 for the `BL` and `KEM` public key, respectively.

The `alg` parameter, when present,
defines the `alg` parameter of ARKG derived public keys derived from this ARKG public seed.

The following CDDL [RFC8610] example represents an `ARKG-P256ADD-ECDH` public seed
restricted to generating derived public keys for use with the ESP256 [I-D.jose-fully-spec-algs] signature algorithm:

~~~cddl
{
  1: -65537,   ; kty: ARKG-pub
               ; kid: Opaque identifier
  2: h'60b6dfddd31659598ae5de49acb220d8
       704949e84d484b68344340e2565337d2',
  3: -9,       ; alg: ESP256

  -1: {        ; BL public key
    1: 2,      ; kty: EC2
    -1: 1,     ; crv: P256
    -2: h'69380FC1C3B09652134FEEFBA61776F9
          7AF875CE46CA20252C4165102966EBC5',
    -3: h'8B515831462CCB0BD55CBA04BFD50DA6
          3FAF18BD845433622DAF97C06A10D0F1',
  },

  -2: {        ; KEM public key
    1: 2,      ; kty: EC2
    -1: 1,     ; crv: P256
    -2: h'5C099BEC31FAA581D14E208250D3FFDA
          9EC7F543043008BC84967A8D875B5D78',
    -3: h'539D57429FCB1C138DA29010A155DCA1
          4566A8F55AC2F1780810C49D4ED72D58',
  }
}
~~~

The following is the same example encoded as CBOR:

~~~
h'a5013a0001000002582060b6dfddd31659598ae5de49acb220d8704949e84d48
  4b68344340e2565337d2032820a40102200121582069380fc1c3b09652134fee
  fba61776f97af875ce46ca20252c4165102966ebc52258208b515831462ccb0b
  d55cba04bfd50da63faf18bd845433622daf97c06a10d0f121a4010220012158
  205c099bec31faa581d14e208250d3ffda9ec7f543043008bc84967a8d875b5d
  78225820539d57429fcb1c138da29010a155dca14566a8f55ac2f1780810c49d
  4ed72d588'
~~~


## References to ARKG derived private keys {#cose-arkg-derived-refs}

A reference to a private key derived using ARKG
may be represented as a `COSE_Key_Ref` structure [I-D.lundberg-cose-2p-algs]
whose `kty` is `TBD` (Ref-ARKG-derived, placeholder -65538).
This key reference type defines key type parameters -1 and -2 respectively
for the `kh` and `info` parameters of `ARKG-Derive-Private-Key`.
The `kid` (2) parameter identifies the ARKG private seed `sk`.
Thus the `COSE_Key_Ref` structure conveys all arguments to use in `ARKG-Derive-Private-Key`
to acquire the referenced private key.

A `COSE_Key_Ref` structure whose `kty` is TBD (Ref-ARKG-derived, placeholder -65538)
MUST include the parameters `kh` (-1) and `info` (-2) defined in {{tbl-ref-arkg-params}}.

{: #tbl-ref-arkg-params title="COSE_Key_Ref parameters for the Ref-ARKG-derived type."}
| Name | COSE Value | Description |
| ---- | ---------- | ----------- |
| kh   | -1         | `kh` argument to `ARKG-Derive-Private-Key` |
| info | -2         | `info` argument to `ARKG-Derive-Private-Key` |

The following CDDL example represents a reference to a key derived by `ARKG-P256ADD-ECDH`
and restricted for use with the ESP256 [I-D.jose-fully-spec-algs] signature algorithm:

~~~cddl
{
  1: -65538,   ; kty: Ref-ARKG-derived
               ; kid: Opaque identifier of ARKG-pub
  2: h'60b6dfddd31659598ae5de49acb220d8
       704949e84d484b68344340e2565337d2',
  3: -65539,   ; alg: ESP256-ARKG

               ; ARKG-P256ADD-ECDH key handle
               ; (HMAC-SHA-256-128 followed by
                  SEC1 uncompressed ECDH public key)
  -1: h'ae079e9c52212860678a7cee25b6a6d4
        048219d973768f8e1adb8eb84b220b0ee3
          a2532828b9aa65254fe3717a29499e9b
          aee70cea75b5c8a2ec2eb737834f7467
          e37b3254776f65f4cfc81e2bc4747a84',

               ; info argument to ARKG-Derive-Private-Key
  -2: 'Example application info',
}
~~~

The following is the same example encoded as CBOR:

~~~
h'a5013a0001000102582060b6dfddd31659598ae5de49acb220d8704949e84d48
  4b68344340e2565337d2033a00010002205851ae079e9c52212860678a7cee25
  b6a6d4048219d973768f8e1adb8eb84b220b0ee3a2532828b9aa65254fe3717a
  29499e9baee70cea75b5c8a2ec2eb737834f7467e37b3254776f65f4cfc81e2b
  c4747a842158184578616d706c65206170706c69636174696f6e20696e666f'
~~~


# Security Considerations {#Security}

TODO


# Privacy Considerations {#Privacy}

TODO


# IANA Considerations {#IANA}

## COSE Key Types Registrations

This section registers the following values in the IANA "COSE Key Types" registry [IANA.COSE].

- Name: ARKG-pub
  - Value: TBD (Placeholder -65537)
  - Description: ARKG public seed
  - Capabilities: \[kty(-65537), pk_bl, pk_kem\]
  - Reference: {{cose-arkg-pub-seed}} of this document

- Name: Ref-ARKG-derived
  - Value: TBD (Placeholder -65538)
  - Description: Reference to private key derived by ARKG
  - Capabilities: \[kty(-65538), kh\]
  - Reference: [I-D.lundberg-cose-2p-algs], {{cose-arkg-derived-refs}} of this document

These registrations add the following choices to the CDDL [RFC8610] type socket `$COSE_kty_ref` [I-D.lundberg-cose-2p-algs]:

~~~cddl
$COSE_kty_ref /= -65538   ; Placeholder value
~~~


## COSE Key Type Parameters Registrations

This section registers the following values in the IANA "COSE Key Type Parameters" registry [IANA.COSE].

- Key Type: TBD (ARKG-pub, placeholder -65537)
  - Name: pk_bl
  - Label: -1
  - CBOR Type: COSE_Key
  - Description: ARKG key blinding public key
  - Reference: {{cose-arkg-pub-seed}} of this document

- Key Type: TBD (ARKG-pub, placeholder -65537)
  - Name: pk_kem
  - Label: -2
  - CBOR Type: COSE_Key
  - Description: ARKG key encapsulation public key
  - Reference: {{cose-arkg-pub-seed}} of this document

- Key Type: TBD (Ref-ARKG-derived, placeholder -65538)
  - Name: kh
  - Label: -1
  - CBOR Type: bstr
  - Description: kh argument to ARKG-Derive-Private-Key
  - Reference: [I-D.lundberg-cose-2p-algs], {{cose-arkg-derived-refs}} of this document

- Key Type: TBD (Ref-ARKG-derived, placeholder -65538)
  - Name: info
  - Label: -2
  - CBOR Type: bstr
  - Description: info argument to ARKG-Derive-Private-Key
  - Reference: [I-D.lundberg-cose-2p-algs], {{cose-arkg-derived-refs}} of this document


# Design rationale

## Using a MAC {#design-rationale-mac}

The ARKG construction by Wilson [Wilson] omits the MAC and instead encodes application context in the PRF labels,
arguing that this leads to invalid keys/signatures in cases that would have a bad MAC.
We choose to keep the MAC from the construction by Frymann et al. [Frymann2020],
but allow it to be omitted in case the chosen KEM already guarantees ciphertext integrity.

The reason for this is to ensure that the delegating party can distinguish key handles that belong to its ARKG seed.
For example, this is important for applications using the W3C Web Authentication API [WebAuthn],
which do not know beforehand which authenticators are connected and available.
Instead, authentication requests may include references to several eligible authenticators,
and the one to use is chosen opportunistically by the WebAuthn client depending on which are available at the time.
Consider using ARKG in such a scenario to sign some data with a derived private key:
a user may have several authenticators and thus several ARKG seeds,
so the signing request might include several well-formed ARKG key handles,
but only one of them belongs to the ARKG seed of the authenticator that is currently connected.
Without an integrity check,
choosing the wrong key handle might cause the `ARKG-Derive-Private-Key` procedure to silently derive the wrong key
instead of returning an explicit error, which would in turn lead to an invalid signature or similar final output.
This would make it difficult or impossible to diagnose the root cause of the issue and present actionable user feedback.
For this reason, we require the KEM to guarantee ciphertext integrity
so that `ARKG-Derive-Private-Key` can fail early if the key handle belongs to a different ARKG seed.

It is straightforward to see that adding the MAC to the construction by Wilson
does not weaken the security properties defined by Frymann et al. [Frymann2020]:
the construction by Frymann et al. can be reduced to the ARKG construction in this document
by instantiating `BL` as described in {{blinding-ec}}
and `KEM` as described in {{kem-ecdh}}.
The use of hash_to_field in {{blinding-ec}} corresponds to the KDF<sub>1</sub> parameter in [Frymann2020],
and the use of HMAC and HKDF in {{hmac-kem}} corresponds to the MAC and KDF<sub>2</sub> parameters in [Frymann2020].
Hence if one can break PK-unlinkability or SK-security of the ARKG construction in this document,
one can also break the same property of the construction by Frymann et al.


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

- 00 Initial Version

- 01 Editorial Fixes to formatting and references.

- 02
  - Rewritten introduction.
  - Renamed ARKG-Derive-Secret-Key to ARKG-Derive-Private-Key.
  - Overhauled EC instantiations to use hash_to_field and account for non-prime order curve key generation.
  - Eliminated top-level MAC and KDF instance parameters.
  - Added info parameter to instance parameter functions.
  - Added requirement of KEM ciphertext integrity and generic formula for augmenting any KEM using HMAC.
  - Added curve/edwards25519/448 instances.
  - Added proposal for COSE bindings and key reference types.

- 03
  - Renamed section "Using HMAC to adapt a KEM without {integrity protection => ciphertext integrity}".
  - Fixed info argument to HMAC in section "Using HMAC to adapt a KEM without ciphertext integrity".
  - Added reference to Shoup for definition of key encapsulation mechanism.
  - Added CDDL definition of COSE_Key_Ref
  - Editorial fixes to references.
  - Renamed proposed COSE Key Types.
