---
stand_alone: true
ipr: trust200902

title: "Split Signing Algorithms for COSE"
abbrev: "Split Signing Algorithms for COSE"
lang: en
category: std

docname: draft-lundberg-cose-two-party-signing-algs-latest
submissiontype: IETF  # also: "independent", "editorial", "IAB", or "IRTF"
number:
date:
consensus: true
v: 3
area: "Security"
workgroup: "COSE"
keyword:
 - COSE
 - Signing
 - Algorithms
 - Split Algorithms
 - Split Signing
 - ARKG

venue:
  group: "COSE"
  type: "Working Group"
  mail: "cose@ietf.org"
  arch: "https://mailarchive.ietf.org/arch/browse/cose/"
  github: "YubicoLabs/cose-two-party-signing-algs-rfc"


author:
- role: editor
  fullname: Emil Lundberg
  organization: Yubico
  street: Gävlegatan 22
  city: Stockholm
  country: SE
  email: emil@emlun.se

- fullname: Michael B. Jones
  ins: M.B. Jones
  organization: Self-Issued Consulting
  email: michael_b_jones@hotmail.com
  uri: https://self-issued.info/
  country: United States

normative:
  I-D.bradleylundberg-ARKG: I-D.draft-bradleylundberg-cfrg-arkg
  IANA.COSE:
    target: https://www.iana.org/assignments/cose/
    title: CBOR Object Signing and Encryption (COSE)
    author:
    - org: IANA
  RFC2119:
  RFC8032:
  RFC8174:
  RFC8610:
  RFC9052:
  RFC9864:
  SEC1:
    target: https://www.secg.org/sec1-v2.pdf
    author:
    - org: Certicom Research
    date: May 2009
    title: "SEC 1: Elliptic Curve Cryptography"

informative:
  FALCON:
    target: https://falcon-sign.info/
    title: 'FALCON: Fast-Fourier Lattice-based Compact Signatures over NTRU'
    author:
    - fullname: Pierre-Alain Fouque
    - fullname: Jeffrey Hoffstein
    - fullname: Paul Kirchner
    - fullname: Vadim Lyubashevsky
    - fullname: Thomas Pornin
    - fullname: Thomas Prest
    - fullname: Thomas Ricosset
    - fullname: Gregor Seiler
    - fullname: William Whyte
    - fullname: Zhenfei Zhang
    date: 2017
  FIPS-201:
    target: https://csrc.nist.gov/pubs/fips/201-3/final
    title: 'Personal Identity Verification (PIV) of Federal Employees and Contractors'
    author:
    - org: National Institute of Standards and Technology
    date: 2022
  FIPS-204:
    target: https://nvlpubs.nist.gov/nistpubs/FIPS/NIST.FIPS.204.pdf
    title: Module-Lattice-Based Digital Signature Standard
    author:
    - org: National Institute of Standards and Technology
    date: August 2024
  FIPS-186-5:
    target: https://nvlpubs.nist.gov/nistpubs/FIPS/NIST.FIPS.186-5.pdf
    title: Digital Signature Standard (DSS)
    author:
    - org: National Institute of Standards and Technology
    date: February 2023
  I-D.COSE-Hash-Envelope: I-D.draft-ietf-cose-hash-envelope
  NIST-SP-800-73-5:
    target: https://doi.org/10.6028/NIST.SP.800-73pt2-5
    title: 'Interfaces for Personal Identity Verification: Part 2 – PIV Card Application Card Command Interface'
    author:
    - fullname: Hildegard Ferraiolo
      org: National Institute of Standards and Technology, Gaithersburg, MD
    - fullname: Ketan Mehta
      org: National Institute of Standards and Technology, Gaithersburg, MD
    - fullname: Salvatore Francomacaro
      org: National Institute of Standards and Technology, Gaithersburg, MD
    - fullname: Ramaswamy Chandramouli
      org: National Institute of Standards and Technology, Gaithersburg, MD
    - fullname: Sarbari Gupta
      org: National Institute of Standards and Technology, Gaithersburg, MD
    date: 2024
    refcontent: NIST Special Publication (SP) NIST SP 800-73pt2-5
  PKCS11-Spec-v3.1:
    target: https://docs.oasis-open.org/pkcs11/pkcs11-spec/v3.1/os/pkcs11-spec-v3.1-os.html
    title: 'PKCS #11 Specification Version 3.1.'
    author:
    - fullname: Dieter Bong
    - fullname: Tony Cox
    date: 2023-07-23
    refcontent: OASIS Standard
    ann: 'Latest stage: <https://docs.oasis-open.org/pkcs11/pkcs11-spec/v3.1/pkcs11-spec-v3.1.html>.'
  OPENPGPCARD:
    target: https://gnupg.org/ftp/specs/OpenPGP-smart-card-application-3.4.1.pdf
    title: Functional Specification of the OpenPGP application on ISO Smart Card Operating Systems
    author:
    - fullname: Achim Pietig
    date: March 2020
    refcontent: Version 3.4.1
  RFC1958:
  RFC9380:
  RFC9413:
  RFC9881:
  SECDSA:
    target: https://eprint.iacr.org/2021/910
    title: 'SECDSA: Mobile signing and authentication under classical "sole control"'
    author:
    - fullname: Eric Verheul
    date: July 2021


--- abstract

This specification defines COSE algorithm identifiers
for negotiating how to split a signature algorithm between two cooperating parties.
Typically the first party hashes the data to be signed
and the second party finishes the signature over the hashed data.
This is a common technique, useful for example when the signing private key is held in a smart card
or similar hardware component with limited processing power and communication bandwidth.
The resulting signatures are identical in structure to those computed by a single party,
and can be verified using the same verification algorithm
without additional steps to preprocess the signed data.

--- middle

{:emlun: source="Emil"}

# Introduction

CBOR Object Signing and Encryption (COSE) [RFC9052]
algorithm identifiers are used for algorithm negotiation
and to annotate cryptographic objects with how to interpret them,
for example which algorithm to use to verify a signature or decapsulate a shared key.
Existing COSE algorithm identifiers omit some internal details of how the object was constructed,
since those details are typically irrelevant for the recipient.

The algorithm identifiers defined in this specification are meant for a complementary use case:
to divide responsibilities during _construction_ of a cryptographic object,
instead of describing how to _consume_ the object.
Specifically, they provide an interoperable way to negotiate
how a signing operation is split between two cooperating parties,
for example, a smart card and a software application,
while the verification algorithm for the resulting signature remains the same
as if the signature was created by a single party.
These split algorithm identifiers are therefore not meant for annotating signature objects,
since the verification algorithm is better indicated using already existing algorithm identifiers.

As mentioned above, a primary use case for this is for algorithm negotiation
between a software application and a smart card or other hardware security module (HSM) holding the signing private key.
Since the HSM may have limited processing power and communication bandwidth,
it may not be practical to send the entire original message to the HSM.
Instead, since most signature algorithms begin with digesting the message
into a fixed-length intermediate input, this initial digest can be computed by the software application
while the HSM performs the rest of the signature algorithm on the digest.
This is a common technique used in standards such as OpenPGP [OPENPGPCARD],
PKCS #11 [PKCS11-Spec-v3.1], and PIV [NIST-SP-800-73-5].

Since different signature algorithms digest the message in different ways
and at different stages of the algorithm,
it is not possible for a cryptographic API to specify that, for example, "the hash digest is computed by the caller"
generically for all algorithms.
Security considerations for this split may also differ between algorithms.
Instead, the algorithm identifiers defined in this specification
enable the parties of that cryptographic API to signal precisely, for each signature algorithm individually,
which steps of the algorithm are performed by which party.
We thus define two roles:
the _digester_ (e.g., a software application) that initializes the signing procedure,
and the _signer_ (e.g., an HSM) that holds exclusive control of the signing private key.

Note that these algorithm identifiers do not define new "pre-hashed" variants of the base signature algorithm,
nor an intermediate "hash envelope" data structure, such as that defined in [I-D.COSE-Hash-Envelope].
Rather, these identifiers denote existing signature algorithms
that would typically be executed by a single party,
but split into two stages.

Some signature algorithms,
such as PureEdDSA [RFC8032],
by their design, cannot be split in this way, and therefore cannot be assigned split signing algorithm identifiers.
However, if such a signature algorithm defines a "pre-hashed" variant,
that "pre-hashed" algorithm can be assigned a split signing algorithm identifier,
enabling the pre-hashing step to be performed by the _digester_
and the remaining steps by the _signer_.
For example, this specification defines Ed25519ph-split ({{eddsa-split}}) as a split variant of Ed25519ph [RFC8032].
Note that Ed25519 and Ed25519ph have distinct verification algorithms,
but Ed25519ph and Ed25519ph-split use the same verification algorithm.


## Requirements Notation and Conventions

The key words "MUST", "MUST NOT", "REQUIRED", "SHALL", "SHALL NOT", "SHOULD", "SHOULD NOT", "RECOMMENDED", "NOT RECOMMENDED", "MAY", and "OPTIONAL" in this document are to be interpreted as described in BCP 14 [RFC2119] [RFC8174] when, and only when, they appear in all capitals, as shown here.


## Prior Art

Split signing is a common technique used in existing smart card standards.
The following subsections expand on how the technique is applied in OpenPGP [OPENPGPCARD],
PKCS #11 [PKCS11-Spec-v3.1], and PIV [NIST-SP-800-73-5].


### OpenPGP

The OpenPGP smart card protocol [OPENPGPCARD]
defines the format of signing commands in section "7.2.10 PSO: COMPUTE DIGITAL SIGNATURE":

>**7.2.10 PSO: COMPUTE DIGITAL SIGNATURE**
>
>The command for digital signature computation is shown in the table below.
>The hash value (ECDSA) or the DigestInfo is delivered in the data field of the command. \[...\]

The "Data field" parameter is subsequently defined as "Data to be integrated in the DSI: hash value (ELC) or DigestInfo (RSA)".
Thus both ECDSA and RSA signatures are computed jointly by the host computing the digest of the signed data
and the smart card finalizing the signature on the digest;
the host acts as _digester_ and the smart card acts as _signer_.

TODO: Spec 3.4.1 only covers ECDSA and RSA, but some implementations also support Ed25519.
Identify and include good references for how OpenPGP smart cards handle Ed25519.


### PKCS #11

PKCS #11 [PKCS11-Spec-v3.1]
defines signing commands in sections "5.13 Signing and MACing functions" and "5.14 Message-based signing and MACing functions".
These sections define `C_SignInit` and `C_MessageSignInit` functions that both take a `pMechanism` parameter indicating the signature mechanism.
Mechanisms are defined in section "6 Mechanisms", which notably includes the subsections
"6.3.12 ECDSA without hashing" and "6.3.13 ECDSA with hashing":

>**6.3.12 ECDSA without hashing**
>
>\[...\]
>
>The ECDSA without hashing mechanism, denoted **CKM_ECDSA**, is a mechanism for single-part signatures and verification for ECDSA.
>(This mechanism corresponds only to the part of ECDSA that processes the hash value, which should not be longer than 1024 bits;
>it does not compute the hash value.)
>
>\[...\]

>**6.3.13 ECDSA with hashing**
>
>\[...\]
>
>The ECDSA with SHA-1, SHA-224, SHA-256, SHA-384, SHA-512, SHA3-224, SHA3-256, SHA3-384, SHA3-512 mechanism,
>denoted **CKM_ECDSA_\[SHA1|SHA224|SHA256|SHA384|SHA512|SHA3_224|SHA3_256|SHA3_384|SHA3_512\]** respectively,
>is a mechanism for single- and multiple-part signatures and verification for ECDSA.
>This mechanism computes the entire ECDSA specification, including the hashing with
>SHA-1, SHA-224, SHA-256, SHA-384, SHA-512, SHA3-224, SHA3-256, SHA3-384, SHA3-512 respectively.
>
>\[...\]

Thus PKCS #11 supports both split signing using the **CKM_ECDSA** mechanism
and "non-split" signing using the **CKM_ECDSA_SHA\*** mechanisms;
when using **CKM_ECDSA**,
the PKCS #11 caller acts as _host_ and the Cryptoki implementation acts as _signer_.


### PIV: FIPS-201, NIST SP 800

NIST Special Publication 800 [NIST-SP-800-73-5]
contains technical specifications for the Personal Identity Verification (PIV) standard [FIPS-201],
and defines the format of signing commands in section "3.2.4. GENERAL AUTHENTICATE Card Command":

>**3.2.4. GENERAL AUTHENTICATE Card Command**
>\[...\]
>
>The GENERAL AUTHENTICATE command SHALL be used with the digital signature key ('9C') to
>realize the signing functionality on the PIV client application programming interface. Data to be
>signed is expected to be hashed off-card. Appendix A.4 illustrates the use of the GENERAL
>AUTHENTICATE command for signature generation.
>
>\[...\]

Appendix A.4 gives examples of RSA and ECDSA signature generation commands.
For RSA the command needs to be sent in two parts,
giving the "Data Field" argument first as "'7C' – L1 { '82' '00' '81' L2 {first part of the PKCS #1 v1.5 or PSS padded message hash value }}"
and then "{second and last part of the PKCS #1 v1.5 or PSS padded message hash value}";
for ECDSA the "Data Field" argument is given as "'7C' – L1 { '82' '00' '81' L2 {hash value of message}}".

Thus both ECDSA and RSA signatures are computed jointly by the host computing the digest of the signed data
and the smart card finalizing the signature on the digest;
the host acts as _digester_ and the smart card acts as _signer_.


# Split Signing Algorithms {#split-algs}

This section defines divisions of signing algorithm steps between a _digester_ and a _signer_
in a split signing protocol,
and assigns algorithm identifiers to these algorithm divisions.
The _digester_ performs the first part of the split algorithm and does not have access to the signing private key,
while the _signer_ performs the second part of the split algorithm and has access to the signing private key.
For signing algorithms that format the message to insert domain separation tags,
as described in {{Section 2.2.5 of RFC9380}},
this message formatting is also performed by the _signer_.

How the digest, and any related `COSE_Sign_Args` structure (see {{cose-sign-args}}),
are transported from _digester_ to _signer_ is out of scope for this specification,
but it is expected that the digest will usually be transmitted as the "data to be signed" argument.

The algorithm identifiers defined in this specification with "-split" in their names
MAY appear in COSE structures used internally between the _digester_ and the _signer_ in a split signing protocol,
but SHOULD NOT appear in COSE structures consumed by signature verifiers.
COSE structures consumed by signature verifiers
SHOULD instead use the corresponding conventional algorithm identifiers for the verification algorithm.
These are listed in the "Verification algorithm" column in the tables defining split signing algorithm identifiers.

The following subsections define an initial set of split signing algorithm identifiers.
The last subsection provides guidance for defining additional identifiers beyond this initial set.


## ECDSA {#ecdsa-split}

ECDSA [FIPS-186-5] split signing uses the following division between the _digester_ and the _signer_
of the steps of the ECDSA signature generation algorithm [FIPS-186-5]:

- The signing procedure is defined in Section 6.4.1 of [FIPS-186-5].
- The _digester_ performs Step 1 of the signing procedure - hashing the message, producing the value _H_.
- The message input to the _signer_ is the value _H_ defined in the signing procedure.
- The _signer_ resumes the signing procedure from Step 2.

The following algorithm identifiers are defined:

{: #tbl-ecdsa-split title="ECDSA split signing algorithm values."}
| Name         | COSE Value | Verification algorithm | Description |
| ------------ | ---------- | ---------------------- | ----------- |
| ESP256-split | TBD        | ESP256                 | ESP256 split signing as defined in {{ecdsa-split}}
| ESP384-split | TBD        | ESP384                 | ESP384 split signing as defined in {{ecdsa-split}}
| ESP512-split | TBD        | ESP512                 | ESP512 split signing as defined in {{ecdsa-split}}


Note: This is distinct from the similarly named Split-ECDSA (SECDSA) [SECDSA],
although SECDSA can be implemented using this split procedure as a component.


## HashEdDSA {#eddsa-split}

Split HashEdDSA [RFC8032] uses the following division between the _digester_ and the _signer_
of the steps of the HashEdDSA signing algorithm [RFC8032]:

- HashEdDSA is a combination of the EdDSA signing procedure and the PureEdDSA signing procedure.
  The EdDSA signing procedure is defined in the first paragraph of {{Section 3.3 of RFC8032}}.
  The PureEdDSA signing procedure is defined in the second paragraph of {{Section 3.3 of RFC8032}}.
- The _digester_ computes the value `PH(M)` defined in the EdDSA signing procedure.
- The message input to the _signer_ is the value `PH(M)` defined in the EdDSA signing procedure.
  This value is represented as `M` in the PureEdDSA signing procedure.
- The _signer_ executes the PureEdDSA signing procedure,
  where the value denoted `M` in the PureEdDSA signing procedure
  takes the value denoted `PH(M)` in the EdDSA signing procedure.

PureEdDSA [RFC8032] cannot be divided in this way
since such a division would require that the _digester_ has access to the private key.

The following algorithm identifiers are defined:

{: #tbl-eddsa-split title="HashEdDSA algorithm values."}
| Name            | COSE Value | Verification algorithm | Description |
| --------------- | ---------- | ---------------------- | ----------- |
| Ed25519ph       | TBD        | Ed25519ph              | EdDSA using the Ed25519ph parameter set in {{Section 5.1 of RFC8032}} |
| Ed25519ph-split | TBD        | Ed25519ph              | EdDSA using the Ed25519ph parameter set in {{Section 5.1 of RFC8032}} and split as defined in {{eddsa-split}} |
| Ed448ph         | TBD        | Ed448ph                | EdDSA using the Ed448ph parameter set in {{Section 5.2 of RFC8032}} |
| Ed448ph-split   | TBD        | Ed448ph                | EdDSA using the Ed448ph parameter set in {{Section 5.2 of RFC8032}} and split as defined in {{eddsa-split}} |


## Defining Split Signing Algorithms {#defining-split-algs}

Future definitions of additional split signing algorithm identifiers
SHOULD follow the conventions established in {{split-algs}} as far as possible.
For example, if a signature algorithm prescribes insertion of domain separation tags
in a way that requires processing the entirety of the data to be signed,
it might be necessary to delegate the domain separation responsibility to the _digester_.
Per the considerations in {{sec-cons-trusted-roles-comp}},
split signing algorithm identifiers SHOULD be defined in ways that minimize
how much responsibility is delegated to the _digester_.

As a concrete example, consider ML-DSA and HashML-DSA [FIPS-204].
ML-DSA and HashML-DSA prefix the input data with a 0 octet and a 1 octet respectively,
which enforces domain separation between ML-DSA and HashML-DSA signatures.
{{Appendix D of RFC9881}} describes a mode of ML-DSA
that could be assigned a split signing algorithm identifier
where the _digester_ performs `Computeμ` and the _signer_ performs `Signμ`.
Note that this puts the _digester_ in control of the domain separation tags;
this is necessary if the hash step is not performed by the _signer_.
Therefore with this construction, it is the _digester_ that decides
whether the signing protocol will produce an ML-DSA signature or a HashML-DSA signature.
In contrast, HashML-DSA first hashes the input data alone and then another time with domain separation tags;
therefore HashML-DSA can be assigned a split signing algorithm identifier
that keeps the _signer_ in control of the domain separation tags
and ensures that the signing protocol can only produce HashML-DSA signatures.


# COSE Signing Arguments {#cose-sign-args}

While many signature algorithms take the private key and data to be signed as the only two parameters,
some signature algorithms have additional parameters that must also be set.
For example,
to sign using a key derived by ARKG [I-D.bradleylundberg-ARKG],
two additional arguments `kh` and `ctx` are needed in `ARKG-Derive-Private-Key` to derive the signing private key.

While such additional arguments are simple to provide to the API of the signing procedure in a single-party context,
in a split signing context these additional arguments also need to be conveyed from the _digester_ to the _signer_.
For this purpose, we define a new COSE structure `COSE_Sign_Args` for "COSE signing arguments".
This enables defining a unified, algorithm-agnostic protocol between the _digester_ and the _signer_,
rather than requiring a distinct protocol for each signature algorithm for the sake of conveying algorithm-specific parameters.

`COSE_Sign_Args` is built on a CBOR map.
The set of common parameters that can appear in a `COSE_Sign_Args`
can be found in the IANA "COSE Signing Arguments Common Parameters" registry {{common-params-reg}}.
Additional parameters defined for specific signing algorithms
can be found in the IANA "COSE Signing Arguments Algorithm Parameters" registry {{alg-params-reg}}.

The CDDL grammar describing `COSE_Sign_Args`, using the CDDL fragment defined in {{Section 1.5 of RFC9052}}, is:

~~~cddl
COSE_Sign_Args = {
    3 ^ => tstr / int,  ; alg
    * label => values,
}
~~~


## COSE Signing Arguments Common Parameters {#cose-sign-args-common}

This document defines a set of common parameters for a COSE Signing Arguments object.
{{tbl-cose-sign-args-common}} provides a summary of the parameters defined in this section.

{: #tbl-cose-sign-args-common title="Common parameters of the COSE_Sign_Args structure."}
| Name | Label | CBOR Type  | Value Registry  | Description |
| ---- | ----- | ---------- | --------------- | ----------- |
| alg  | 3     | tstr / int | COSE Algorithms | Signing algorithm to use |

- alg: This parameter identifies the signing algorithm the additional arguments apply to.
  The signer MUST verify that this algorithm matches any key usage restrictions set on the key to be used.
  If the algorithms do not match, then the signature operation MUST be aborted with an error.

Definitions of COSE algorithms MAY define additional algorithm-specific parameters for `COSE_Sign_Args`.

The following CDDL example conveys additional arguments for signing data
using the ESP256-split algorithm (see {{ecdsa-split}})
and a key derived using `ARKG-P256` [I-D.bradleylundberg-ARKG]:

~~~cddl
{
  3: -65539,   ; alg: ESP256-split with ARKG-P256 (placeholder value)

               ; ARKG-P256 key handle
               ; (HMAC-SHA-256-128 followed by
                  SEC1 uncompressed ECDH public key)
  -1: h'27987995f184a44cfa548d104b0a461d
        0487fc739dbcdabc293ac5469221da91b220e04c681074ec4692a76ffacb9043de
          c2847ea9060fd42da267f66852e63589f0c00dc88f290d660c65a65a50c86361',

               ; ctx argument to ARKG-Derive-Private-Key
  -2: 'ARKG-P256.test vectors',
}
~~~


# Security Considerations {#security-cons}

## Protocol-Level Trusted Roles {#sec-cons-trusted-roles-protocol}

This specification assumes that both the _digester_ and _signer_ roles
described in {{split-algs}} are trusted and cooperate honestly.
This is because a similar division between "application" and "secure element"
typically exists already:
even if all steps of the signing algorithm are executed in a trusted secure element,
the inputs to the secure element are provided by some outside component such as a software application.
If the application can provide any input to be signed,
then for all practical purposes it is trusted with possession of any private keys
for as long as it is authorized to exercise the secure element.
The application can in practice obtain a signature over any chosen message
without needing to perform a forgery attack.
The same relationship exists between _digester_ and _signer_.
Applications that cannot trust an external _digester_ -
for example a hardware security device with an integrated secure display of what data is about to be signed -
by definition have no use for split signing algorithm identifiers.

Similarly from a verifier's perspective,
these split signing procedures are implementation details.
When a signature is generated by a single party,
that single party takes on both the _digester_ and the _signer_ roles,
and obviously trusts itself to perform the _digester_ role honestly.
From the verifier's perspective,
a malicious _digester_ in the split signing model would have the same powers
as a malicious signature generator in a single-party signing model.
Thus, on the application or protocol level,
assuming an honest _digester_ is no more restrictive than assuming an honest signature generator.


## Component-Level Trusted Roles {#sec-cons-trusted-roles-comp}

The reasoning in {{sec-cons-trusted-roles-protocol}} does not hold on the component level.
A _signer_ implementation MUST NOT assume that the _digester_ implementation
it interoperates with is necessarily honest.
Split signing algorithms MUST NOT be defined in a way
that enables a malicious _digester_ with access to an honest _signer_ to produce forgeries -
any that could not be produced by simply requesting a signature over the desired message -
or extract secrets from the _signer_.

For example, for ECDSA ({{ecdsa-split}}), a malicious _digester_ can choose _H_
in such a way that the _signer_ will derive any _digester_-chosen value of _e_,
including zero or other potentially problematic values.
Fortunately, in this case, this does not enable the _digester_ to extract the signature nonce or private key.
It also does not make forgeries easier,
since the _digester_ still needs to find a preimage of _e_ for the relevant hash function.
Definitions of other algorithms need to ensure that similar chosen-input attacks
do not enable extracting secrets or forging protocol-level messages.

For example, a naively prehashed version of FALCON [FALCON] would allow such a key compromise:
A FALCON signature is a value `s` such that both `s` and `s * h - hash(r || m)` are short,
where `h` is the public key and `r` a randomizer.
If the digester gets to query the signer for signatures of arbitrary stand-ins for `hash(r || m)`,
they can extract the private key by for example asking for repeated signatures of 0.
Therefore, definitions of split signing algorithms need to be reviewed and potentially have security proofs adjusted.


## Incorrect Use of Split Signing Algorithm Identifiers {#sec-cons-invalid-alg-use}

{{split-algs}} recommends against exposing split signing algorithm identifiers -
including those defined in this specification with "-split" in their names -
to signature verifiers.
For example, they should not appear as the "alg" parameter of a COSE_Key public key sent to a signature verifier.
If a split signing algorithm identifier is encountered in an invalid context like this,
the recipient SHOULD reject the message with a fatal error.

This is because the purpose of these split signing algorithm identifiers
is to enable more flexible production of signatures that can be verified by existing implementations of existing verification algorithms.
A prevalence of these identifiers appearing outside the split signing context would defeat this purpose;
we therefore recommend such use SHOULD NOT be tolerated.

This recommendation is the opposite of the oft-cited "robustness principle" stated in paragraph 3.9 of [RFC1958].
Implementations MAY choose to instead follow the robustness principle and tolerate incorrect use of split signing algorithm identifiers,
instead interpreting the identifier as referencing the defined corresponding verification algorithm.
Note however that this is no longer considered a best practice and is likely to harm interoperability [RFC9413].

A verifier's choice to tolerate or not tolerate incorrect use of split signing algorithm identifiers
is expected to not affect security,
assuming a split algorithm identifier is interpreted as an alias representing the same verification algorithm as a non-split algorithm identifier.


# Implementation Considerations {#impl-cons}

## Using Non-Split Signing Algorithm Identifiers in a Split Signing Protocol {#impl-cons-non-split-algs}

A protocol designed to use split signing algorithm identifiers such as those defined in this specification
MAY also allow use of algorithm identifiers that do not represent split signing algorithms.
In this case, the _signer_ performs all steps of the signing procedure as usual.
For example, if the _signer_ receives a signature request with an the algorithm identifier "ESP256",
then the _digester_ passes the input data through unmodified
and it is the _signer_ that computes the SHA-256 digest of the input data as defined in the ESP256 definition [RFC9864].


# IANA Considerations {#IANA}

## COSE Algorithms Registrations {#cose-alg-reg}

This section registers the following values in the IANA "COSE Algorithms" registry [IANA.COSE]:

- Name: ESP256-split
  - Value: TBD (Requested Assignment -300)
  - Description: ESP256 split signing
  - Capabilities: \[kty\]
  - Change Controller: IETF
  - Reference: {{ecdsa-split}} of this specification
  - Recommended: Yes

- Name: ESP384-split
  - Value: TBD (Requested Assignment -301)
  - Description: ESP384 split signing
  - Capabilities: \[kty\]
  - Change Controller: IETF
  - Reference: {{ecdsa-split}} of this specification
  - Recommended: Yes

- Name: ESP512-split
  - Value: TBD (Requested Assignment -302)
  - Description: ESP512 split signing
  - Capabilities: \[kty\]
  - Change Controller: IETF
  - Reference: {{ecdsa-split}} of this specification
  - Recommended: Yes

- Name: Ed25519ph
  - Value: TBD
  - Description: EdDSA using the Ed25519ph parameter set in {{Section 5.1 of RFC8032}}
  - Capabilities: \[kty\]
  - Change Controller: IETF
  - Reference: {{Section 5.1 of RFC8032}}
  - Recommended: Yes

- Name: Ed25519ph-split
  - Value: TBD (Requested Assignment -303)
  - Description: Ed25519ph split as defined in {{eddsa-split}}
  - Capabilities: \[kty\]
  - Change Controller: IETF
  - Reference: {{eddsa-split}} of this specification
  - Recommended: Yes

- Name: Ed448ph
  - Value: TBD
  - Description: EdDSA using the Ed448ph parameter set in {{Section 5.2 of RFC8032}}
  - Capabilities: \[kty\]
  - Change Controller: IETF
  - Reference: {{Section 5.2 of RFC8032}}
  - Recommended: Yes

- Name: Ed448ph-split
  - Value: TBD (Requested Assignment -304)
  - Description: Ed448ph split as defined in {{eddsa-split}}
  - Capabilities: \[kty\]
  - Change Controller: IETF
  - Reference: {{eddsa-split}} of this specification
  - Recommended: Yes


## COSE Signing Arguments Common Parameters Registry {#common-params-reg}

This specification establishes the "COSE Signing Arguments Common Parameters" registry.
The registry uses the "Expert Review Required" registration procedure.
Guidelines for the experts are the same as those in {{Section 11.6 of RFC9052}}.
It should be noted that, in addition to the expert review,
some portions of the registry require a specification,
potentially a Standards Track RFC, be supplied as well.

The columns of the registry are:

Name:
: This is a descriptive name that enables easier reference to the item.
  It is not used in the encoding.

Label:
: The value to be used to identify this algorithm.
  Key map labels MUST be unique.
  The label can be a positive integer, a negative integer, or a string.
  Integer values between 0 and 255 and strings of length 1 are designated as "Standards Action".
  Integer values from 256 to 65535 and strings of length 2 are designated as "Specification Required".
  Integer values of greater than 65535 and strings of length greater than 2 are designated as "Expert Review".
  Integer values in the range -65536 to -1 are
  "used for key parameters specific to a single algorithm delegated
  to the COSE Signing Arguments Algorithm Parameters registry".
  Integer values less than -65536 are marked as private use.

CBOR Type:
: This field contains the CBOR type for the field.

Value Registry:
: This field denotes the registry that values come from, if one exists.

Description:
: This field contains a brief description for the field.

Reference:
: This contains a pointer to the public specification for the field if one exists.

### Initial Contents

The initial contents of this registry are the values in {{tbl-cose-sign-args-common}}.
All of the entries in the "References" column of this registry point to this document.

## COSE Signing Arguments Algorithm Parameters Registry {#alg-params-reg}

This specification establishes the "COSE Signing Arguments Algorithm Parameters" registry.
The registry uses the "Expert Review Required" registration procedure.
Guidelines for the experts are the same as those in {{Section 11.6 of RFC9052}}.

The columns of the table are:

Name:
: This is a descriptive name that enables easier reference to the item.
  It is not used in the encoding.

Label:
: The label is to be unique for every value of key type.
  The range of values is from -65536 to -1.
  Labels are expected to be reused for multiple algorithms.

CBOR Type:
: This field contains the CBOR type for the field.

Required:
: "Required" if parameter is required for this algorithm, otherwise "Optional"

Algorithms:
: Algorithms that this parameter is used with

Description:
: This field contains a brief description for the field.

Reference:
: This contains a pointer to the public specification for the field if one exists.

### Initial Contents

The initial contents of this registry are as follows.
These values come from {{Section 5.3 of I-D.bradleylundberg-ARKG}}.

#### kh

Name:
: kh

Label:
: -1

Cbor Type:
: bstr

Required:
: Required

Algorithms:
: ESP256-ARKG, ESP256-split-ARKG, ESP384-ARKG, ESP384-split-ARKG, ESP512-ARKG, ESP512-split-ARKG, ES256K-ARKG

Description:
: kh argument to ARKG-Derive-Private-Key.

#### ctx

Name:
: ctx

Label:
: -2

Cbor Type:
: bstr

Required:
: Required

Algorithms:
: ESP256-ARKG, ESP256-split-ARKG, ESP384-ARKG, ESP384-split-ARKG, ESP512-ARKG, ESP512-split-ARKG, ES256K-ARKG

Description:
: ctx argument to ARKG-Derive-Private-Key.


# Implementation Status {#impl-status}

This section is to be removed from the specification by the RFC Editor before publication as an RFC.

There are currently two known implementations using features defined by this specification:

- [wwWallet](https://github.com/wwWallet), an EU Digital Identity pilot project.
  wwWallet was entered into the
  ["EUDI Wallet Prototypes" competition held by SprinD GmbH](https://www.sprind.org/en/actions/challenges/eudi-wallet-prototypes),
  and a branch of the wallet was submitted in the competition.
  The competition entry implements ARKG [I-D.bradleylundberg-ARKG]
  for efficiently generating single-use hardware-bound holder binding keys.

  The [implementation](https://github.com/gunet/funke-s3a-wallet-frontend/blob/stage-3/src/services/keystore.ts)
  uses the `COSE_Key_Ref` data structure defined in version 01 of this specification
  in order to send ARKG inputs to a WebAuthn authenticator,
  and uses the placeholder value for the experimental split algorithm identifier ESP256-split-ARKG
  defined in Section 5.2 of [I-D.bradleylundberg-ARKG]
  to negotiate creation and usage of ARKG-derived keys for signing operations.
  Thus wwWallet assumes the _digester_ role while the WebAuthn authenticator assumes the _signer_ role.

- [Yubico](https://www.yubico.com/), a hardware security key vendor,
  has produced limited-availability prototypes of their YubiKey product
  with an ARKG implementation interoperable with wwWallet.
  The YubiKey implementation uses the `COSE_Key_Ref` data structure defined in version 01 of this specification
  to receive ARKG inputs from a WebAuthn Relying Party,
  and uses the placeholder value for the experimental split algorithm identifier ESP256-split-ARKG
  defined in Section 5.2 of [I-D.bradleylundberg-ARKG]
  to negotiate creation and usage of ARKG-derived keys for signing operations.
  Thus the YubiKey assumes the _signer_ role while the WebAuthn Relying Party assumes the _digester_ role.

{{tbl-impl-status-matrix}} summarizes implementation status for individual features.

{: #tbl-impl-status-matrix title="Implementation status of individual features."}
| Feature | Defined by | Digester | Signer |
| ------- | ---------- | -------- | ------ |
| ESP256-split | This specification | - | - |
| ESP384-split | This specification | - | - |
| ESP512-split | This specification | - | - |
| Ed25519ph-split | This specification | - | - |
| Ed448ph-split | This specification | - | - |
| ESP256-split-ARKG | [I-D.bradleylundberg-ARKG] | wwWallet | Yubico |
| ESP384-split-ARKG | [I-D.bradleylundberg-ARKG] | - | - |
| ESP512-split-ARKG | [I-D.bradleylundberg-ARKG] | - | - |
| `COSE_Sign_Args` | This specification | wwWallet | Yubico |


## Dependent Specifications {#impl-status-dependents}

As indicated in the previous section,
the Internet-Draft of ARKG [I-D.bradleylundberg-ARKG] extends this specification with definitions for ARKG:

- Section "5.2 COSE algorithms" defines COSE algorithm identifiers ESP256-split-ARKG, ESP384-split-ARKG
  and ESP512-split-ARKG based on the ECDSA identifiers defined in this specification ({{ecdsa-split}}).
- Section "5.3 COSE signing arguments" defines a representation for ARKG arguments
  using the `COSE_Sign_Args` data structure defined in this specification ({{cose-sign-args}}).


--- back

# Acknowledgements
{: numbered="false"}

We would like to thank
David Dong,
Ilari Liusvaara,
Lucas Prabel,
Sophie Schmieg,
and
Falko Strenzke
for their reviews of and contributions to this specification.


# Document History
{: numbered="false"}

-07

* Populated IANA Considerations sections.

-06

* Added "Prior Art" section to Introduction.

-05

* Fixed ESP384-split misspelled as ESP381-split.
* Clarified that non-"-split" alg IDs defined here may be exposed to verifiers.
* Clarified that transport of digest is out of scope, but expected to be passed as data to be signed.
* Added Security Considerations section "Incorrect Use of Split Signing Algorithm Identifiers".
* Added Implementation Considerations section "Using Non-Split Signing Algorithm Identifiers in a Split Signing Protocol".
* Added section "Defining Split Signing Algorithms" with guidance for handling domain separation tags in new definitions.
* Clarified in introduction that Ed25519 and Ed25519ph(-split) have distinct verification algorithms.
* Clarified in section "Protocol-Level Trusted Roles" why digester is necessarily trusted.
* Clarified in section "Component-Level Trusted Roles" that redundant forgeries are acceptable,
  and added example of key compromise concern for naively hashed FALCON.

-04

* Added Implementation Status section.

-03

* Updated reference to ARKG parameter `info` renamed to `ctx`.
* Refined abstract and introduction to emphasize that the central novelty is not split algorithms as a concept,
  but providing COSE algorithm identifiers for use cases that benefit from such splitting.
* Replaced reference to draft-ietf-jose-fully-specified-algorithms with RFC 9864.
* Added inline definitions of Ed25519ph and Ed448ph registrations,
  replacing speculative references to registrations that do not exist elsewhere.
* Added missing captions to Tables 1 and 2.
* Added Security Considerations section.

-02

* Renamed document from "COSE Algorithms for Two-Party Signing" to "Split signing algorithms for COSE"
  and updated introduction and terminology accordingly.
* Dropped definitions for HashML-DSA, as split variants of ML-DSA are being actively discussed in other IETF groups.
* Changed "Base algorithm" heading in definition tables to "Verification algorithm".
* Remodeled COSE_Key_Ref as COSE_Sign_Args.
  * Dropped definitions of reference types for COSE Key Types registry.

-01

* Added IANA registration requests for algorithms defined.
* Updated references and other editorial tweaks.

-00

* Initial individual draft
