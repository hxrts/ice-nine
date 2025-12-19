# Threshold & Distributed CRYSTALS-Dilithium Signature Schemes

## 1. Two-Party / Threshold Variants of Dilithium

### **DiLizium: A Two-Party Lattice-Based Signature Scheme**

* **Authors:** Jelizaveta Vakarjuk et al. (2021)
* **Description:** A two-party lattice signature protocol based on a variant of CRYSTALS-Dilithium. Offers post-quantum security under Module-LWE/SIS and uses Fiat–Shamir with aborts.
* **Type:** 2-party threshold signature
* **Link:** [https://www.mdpi.com/1099-4300/23/8/989](https://www.mdpi.com/1099-4300/23/8/989) ([cyber.ee][1])

## 2. Two-Party / Practical Threshold Protocol

### **TOPCOAT: Towards Practical Two-Party CRYSTALS-Dilithium**

* **Authors:** Snetkov, Vakarjuk, Laud (2024)
* **Description:** Practical 2-party threshold protocol built on CRYSTALS-Dilithium with public key compression and improved rejection sampling handling.
* **Type:** Efficient 2-party threshold signature
* **Link (Springer):** [https://link.springer.com/article/10.1007/s10791-024-09449-2](https://link.springer.com/article/10.1007/s10791-024-09449-2) ([Springer][2])
* **Alternate PDF:** [https://www.researchsquare.com/article/rs-4383446/v1.pdf](https://www.researchsquare.com/article/rs-4383446/v1.pdf) ([Research Square][3])

## 3. Distributed Threshold Schemes for n-of-n (Full Threshold)

### **Damgård et al. (Distributed Dilithium-G Threshold Signatures)**

* **Scope:** Distributed threshold signatures for n-out-n setting using homomorphic commitments.
* **Note:** Cited as “the first core n-party threshold protocol for Dilithium-G”.
* **Reference discussed in TOPCOAT related work.** ([Springer][2])

## 4. Compact Threshold Signatures (General Lattice)

### **Finally! A Compact Lattice-Based Threshold Signature**

* **Authors:** Guilhem Niot & Rafael del Pino (2025)
* **Description:** Novel threshold scheme achieving signature size near a single Dilithium signature, for small thresholds (T ≤ 8).
* **Highlights:** Efficient signing, signature size close to base Dilithium.
* **Link:** [https://pqshield.com/publications/finally-a-compact-lattice-based-threshold-signature/](https://pqshield.com/publications/finally-a-compact-lattice-based-threshold-signature/) ([PQShield][4])

## 5. Related Work & Context

### **NIST Analysis: Threshold Conversion Challenges**

* **Cozzo & Smart — “Sharing the LUOV: Threshold Post-Quantum Signatures”**
* **Context:** Examines converting PQC schemes (including Dilithium) to threshold forms with generic MPC; notes structural challenges in Dilithium.
* **Link:** [https://csrc.nist.rip/CSRC/media/Events/Second-PQC-Standardization-Conference/documents/accepted-papers/cozzo-luov-paper.pdf](https://csrc.nist.rip/CSRC/media/Events/Second-PQC-Standardization-Conference/documents/accepted-papers/cozzo-luov-paper.pdf) ([NIST Computer Security Resource Center][5])

## 6. Implementation & Prototypes

### **Implementation of a Threshold Post-Quantum Signature (Master’s Theses)**

* Focused on implementing threshold Dilithium using MPC libraries.
* **University of Bern Thesis:** Implementation on real MPC frameworks.
* **Link:** [https://crypto.unibe.ch/theses/2022-post-quandum-threshold-signature/](https://crypto.unibe.ch/theses/2022-post-quandum-threshold-signature/) ([Cryptology and Data Security][6])

## 7. Broader Survey

### **Survey: A Survey on Threshold Digital Signature Schemes**

* **Year:** 2025 (published 2026)
* **Scope:** Comprehensive overview of threshold signature schemes (post-quantum included). Useful for contextual understanding.
* **Link:** [https://link.springer.com/article/10.1007/s11704-025-41297-1](https://link.springer.com/article/10.1007/s11704-025-41297-1) ([Springer][7])
