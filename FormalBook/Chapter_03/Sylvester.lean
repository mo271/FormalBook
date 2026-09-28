/-
Copyright 2026 AItoBit. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: AItoBit
-/
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Nat.Choose.Factorization
import Mathlib.Data.Nat.Factorial.BigOperators
import Mathlib.Data.Nat.Sqrt
import Mathlib.Data.Nat.Totient
import Mathlib.NumberTheory.PrimeCounting
import Mathlib.NumberTheory.Primorial
import Mathlib.Tactic

/-!
# Sylvester's theorem

For `n ≥ 2 * k` and `k > 0` the binomial coefficient `choose n k` has a prime factor `p > k`.

We follow Erdős' approach: if all prime factors of `choose n k` were at most `k`, then the
prime factorisation of `choose n k` gives upper bounds which contradict simple lower bounds.
Small values of `n` are handled by a finite computation.
-/

namespace chapter3.Sylvester

open Nat Finset

/-- The number of primes `≤ x`. -/
def numPrimes (x : ℕ) : ℕ := #{p ∈ range (x + 1) | p.Prime}

/-- A prime `p > k` with a multiple among `n - k + 1, …, n` divides `choose n k`. -/
theorem prime_dvd_choose_of_mod_lt {n k p : ℕ} (hp : p.Prime) (hkp : k < p)
    (hmod : n % p < k) : p ∣ choose n k := by
  have h1 : p ∣ n.descFactorial k := by
    rw [descFactorial_eq_prod_range]
    exact (Nat.dvd_sub_mod n).trans (dvd_prod_of_mem _ (mem_range.mpr hmod))
  rw [descFactorial_eq_factorial_mul_choose] at h1
  rcases (Nat.Prime.dvd_mul hp).mp h1 with h | h
  · exact absurd h (by rw [hp.dvd_factorial]; omega)
  · exact h

/-! ### The finite check

For `n < 4096` we verify by a computation (checked by the kernel) that for every `1 ≤ k ≤ n / 2`
there is a prime `p > k` with `n % p < k`, i.e. a prime `p > k` having a multiple among
`n - k + 1, …, n`. -/

/-- Trial division primality test (only used for numbers `< 65 ^ 2`). -/
def isPrimeB (p : ℕ) : Bool :=
  decide (2 ≤ p) && decide (p < 4225) &&
    (List.range' 2 63).all fun d => decide (p < d * d) || p % d != 0

/-- The primes below `4096`. -/
def primesBelow4096 : List ℕ := [
  2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79, 83, 89,
  97, 101, 103, 107, 109, 113, 127, 131, 137, 139, 149, 151, 157, 163, 167, 173, 179, 181, 191,
  193, 197, 199, 211, 223, 227, 229, 233, 239, 241, 251, 257, 263, 269, 271, 277, 281, 283, 293,
  307, 311, 313, 317, 331, 337, 347, 349, 353, 359, 367, 373, 379, 383, 389, 397, 401, 409, 419,
  421, 431, 433, 439, 443, 449, 457, 461, 463, 467, 479, 487, 491, 499, 503, 509, 521, 523, 541,
  547, 557, 563, 569, 571, 577, 587, 593, 599, 601, 607, 613, 617, 619, 631, 641, 643, 647, 653,
  659, 661, 673, 677, 683, 691, 701, 709, 719, 727, 733, 739, 743, 751, 757, 761, 769, 773, 787,
  797, 809, 811, 821, 823, 827, 829, 839, 853, 857, 859, 863, 877, 881, 883, 887, 907, 911, 919,
  929, 937, 941, 947, 953, 967, 971, 977, 983, 991, 997, 1009, 1013, 1019, 1021, 1031, 1033,
  1039, 1049, 1051, 1061, 1063, 1069, 1087, 1091, 1093, 1097, 1103, 1109, 1117, 1123, 1129,
  1151, 1153, 1163, 1171, 1181, 1187, 1193, 1201, 1213, 1217, 1223, 1229, 1231, 1237, 1249,
  1259, 1277, 1279, 1283, 1289, 1291, 1297, 1301, 1303, 1307, 1319, 1321, 1327, 1361, 1367,
  1373, 1381, 1399, 1409, 1423, 1427, 1429, 1433, 1439, 1447, 1451, 1453, 1459, 1471, 1481,
  1483, 1487, 1489, 1493, 1499, 1511, 1523, 1531, 1543, 1549, 1553, 1559, 1567, 1571, 1579,
  1583, 1597, 1601, 1607, 1609, 1613, 1619, 1621, 1627, 1637, 1657, 1663, 1667, 1669, 1693,
  1697, 1699, 1709, 1721, 1723, 1733, 1741, 1747, 1753, 1759, 1777, 1783, 1787, 1789, 1801,
  1811, 1823, 1831, 1847, 1861, 1867, 1871, 1873, 1877, 1879, 1889, 1901, 1907, 1913, 1931,
  1933, 1949, 1951, 1973, 1979, 1987, 1993, 1997, 1999, 2003, 2011, 2017, 2027, 2029, 2039,
  2053, 2063, 2069, 2081, 2083, 2087, 2089, 2099, 2111, 2113, 2129, 2131, 2137, 2141, 2143,
  2153, 2161, 2179, 2203, 2207, 2213, 2221, 2237, 2239, 2243, 2251, 2267, 2269, 2273, 2281,
  2287, 2293, 2297, 2309, 2311, 2333, 2339, 2341, 2347, 2351, 2357, 2371, 2377, 2381, 2383,
  2389, 2393, 2399, 2411, 2417, 2423, 2437, 2441, 2447, 2459, 2467, 2473, 2477, 2503, 2521,
  2531, 2539, 2543, 2549, 2551, 2557, 2579, 2591, 2593, 2609, 2617, 2621, 2633, 2647, 2657,
  2659, 2663, 2671, 2677, 2683, 2687, 2689, 2693, 2699, 2707, 2711, 2713, 2719, 2729, 2731,
  2741, 2749, 2753, 2767, 2777, 2789, 2791, 2797, 2801, 2803, 2819, 2833, 2837, 2843, 2851,
  2857, 2861, 2879, 2887, 2897, 2903, 2909, 2917, 2927, 2939, 2953, 2957, 2963, 2969, 2971,
  2999, 3001, 3011, 3019, 3023, 3037, 3041, 3049, 3061, 3067, 3079, 3083, 3089, 3109, 3119,
  3121, 3137, 3163, 3167, 3169, 3181, 3187, 3191, 3203, 3209, 3217, 3221, 3229, 3251, 3253,
  3257, 3259, 3271, 3299, 3301, 3307, 3313, 3319, 3323, 3329, 3331, 3343, 3347, 3359, 3361,
  3371, 3373, 3389, 3391, 3407, 3413, 3433, 3449, 3457, 3461, 3463, 3467, 3469, 3491, 3499,
  3511, 3517, 3527, 3529, 3533, 3539, 3541, 3547, 3557, 3559, 3571, 3581, 3583, 3593, 3607,
  3613, 3617, 3623, 3631, 3637, 3643, 3659, 3671, 3673, 3677, 3691, 3697, 3701, 3709, 3719,
  3727, 3733, 3739, 3761, 3767, 3769, 3779, 3793, 3797, 3803, 3821, 3823, 3833, 3847, 3851,
  3853, 3863, 3877, 3881, 3889, 3907, 3911, 3917, 3919, 3923, 3929, 3931, 3943, 3947, 3967,
  3989, 4001, 4003, 4007, 4013, 4019, 4021, 4027, 4049, 4051, 4057, 4073, 4079, 4091, 4093
  ]

/-- Search for a prime `p > k` with `n % p < k` in `primesBelow4096`. -/
def witness (n k : ℕ) : Bool :=
  primesBelow4096.any fun p => decide (k < p) && decide (n % p < k)

/-- For `q ≤ n < q'` the prime `q` itself works for `k > n - q`; the remaining `k` are checked. -/
def blockOK (q q' : ℕ) : Bool :=
  (List.range' q (q' - q)).all fun n =>
    (List.range' 1 (n - q)).all fun k => decide (n < 2 * k) || witness n k

/-- Run `blockOK` on all consecutive pairs of a list, checking that the lower ends are prime. -/
def checkAll : List ℕ → Bool
  | [] => true
  | [_] => true
  | q :: q' :: rest => isPrimeB q && blockOK q q' && checkAll (q' :: rest)

set_option maxRecDepth 100000 in
theorem primes_ok : primesBelow4096.all isPrimeB = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem check_ok : checkAll (primesBelow4096 ++ [4096]) = true := by decide +kernel

theorem isPrimeB_sound (p : ℕ) (h : isPrimeB p = true) : p.Prime := by
  unfold isPrimeB at h
  simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_range'_1,
    Bool.or_eq_true, bne_iff_ne, ne_eq] at h
  obtain ⟨⟨h2, h4225⟩, hd⟩ := h
  rw [Nat.prime_def_le_sqrt]
  refine ⟨h2, fun m hm hms hmd => ?_⟩
  have hmm : m * m ≤ p := Nat.le_sqrt.mp hms
  have hm65 : m < 65 := by nlinarith
  rcases hd m ⟨hm, by omega⟩ with h | h
  · omega
  · exact h (Nat.mod_eq_zero_of_dvd hmd)

theorem witness_sound (n k : ℕ) (h : witness n k = true) :
    ∃ p, p.Prime ∧ k < p ∧ n % p < k := by
  unfold witness at h
  simp only [List.any_eq_true, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨p, hp, h1, h2⟩ := h
  have hall := primes_ok
  rw [List.all_eq_true] at hall
  exact ⟨p, isPrimeB_sound p (hall p hp), h1, h2⟩

theorem blockOK_sound (q q' n k : ℕ) (hq : q.Prime) (hb : blockOK q q' = true) (hqn : q ≤ n)
    (hnq : n < q') (hk : 0 < k) (h2k : 2 * k ≤ n) : ∃ p, p.Prime ∧ k < p ∧ n % p < k := by
  rcases le_or_gt k (n - q) with hkq | hkq
  · unfold blockOK at hb
    simp only [List.all_eq_true, List.mem_range'_1, Bool.or_eq_true, decide_eq_true_eq] at hb
    rcases hb n ⟨hqn, by omega⟩ k ⟨hk, by omega⟩ with h | h
    · omega
    · exact witness_sound n k h
  · refine ⟨q, hq, by omega, ?_⟩
    rw [Nat.mod_eq_sub_mod hqn, Nat.mod_eq_of_lt (by omega)]
    omega

theorem checkAll_sound : ∀ (L : List ℕ) (hL : L ≠ []), checkAll L = true →
    ∀ n, L.head hL ≤ n → n < L.getLast hL →
    ∀ k, 0 < k → 2 * k ≤ n → ∃ p, p.Prime ∧ k < p ∧ n % p < k := by
  intro L
  induction L with
  | nil => intro hL; exact absurd rfl hL
  | cons a l ih =>
    intro _ hc n han hnl k hk h2k
    cases l with
    | nil => simp at han hnl; omega
    | cons b rest =>
      simp only [checkAll, Bool.and_eq_true] at hc
      obtain ⟨⟨hpa, hab⟩, hrest⟩ := hc
      rw [List.getLast_cons_cons] at hnl
      rcases lt_or_ge n b with hnb | hnb
      · exact blockOK_sound a b n k (isPrimeB_sound a hpa) hab han hnb hk h2k
      · exact ih (List.cons_ne_nil _ _) hrest n hnb hnl k hk h2k

theorem small_n (n : ℕ) (hn : n < 4096) (k : ℕ) (hk : 0 < k) (h2k : 2 * k ≤ n) :
    ∃ p, p.Prime ∧ k < p ∧ n % p < k := by
  have hL : primesBelow4096 ++ [4096] ≠ [] := by simp
  have hhead : (primesBelow4096 ++ [4096]).head hL = 2 := rfl
  have hlast : (primesBelow4096 ++ [4096]).getLast hL = 4096 := List.getLast_append_singleton _
  have h2 : 2 ≤ n := by omega
  exact checkAll_sound _ hL check_ok n (hhead ▸ h2) (hlast ▸ hn) k hk h2k

/-! ### Upper bounds when all prime factors are small -/

theorem choose_eq_prod_small (n k T : ℕ) (hkn : k ≤ n) (hTn : T ≤ n)
    (hT : ∀ p, p.Prime → p ∣ choose n k → p ≤ T) :
    choose n k = ∏ p ∈ range (T + 1) with p.Prime, p ^ (choose n k).factorization p := by
  conv_lhs => rw [← prod_pow_factorization_choose n k hkn]
  symm
  apply prod_subset
  · intro p hp; simp only [mem_filter, mem_range] at hp ⊢; omega
  · intro p _ hp
    simp only [mem_filter, mem_range, not_and] at hp
    by_cases hpp : p.Prime
    · have : (choose n k).factorization p = 0 := by
        by_contra h0
        have := hT p hpp (Nat.dvd_of_factorization_pos h0)
        exact absurd hpp (hp (by omega))
      simp [this]
    · simp [Nat.factorization_eq_zero_of_not_prime _ hpp]

theorem choose_le_pow_numPrimes (n k : ℕ) (hkn : k ≤ n)
    (hsmooth : ∀ p, p.Prime → p ∣ choose n k → p ≤ k) :
    choose n k ≤ n ^ numPrimes k := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · have : k = 0 := by omega
    subst this; decide
  rw [choose_eq_prod_small n k k hkn hkn hsmooth]
  apply prod_le_pow_card
  intro p _
  exact pow_factorization_choose_le hn

theorem choose_le_of_smooth (n k : ℕ) (hn : 9 ≤ n) (hkn : 2 * k ≤ n)
    (hsmooth : ∀ p, p.Prime → p ∣ choose n k → p ≤ k) :
    choose n k ≤ n ^ numPrimes (sqrt n) * 4 ^ min k (n / 3) := by
  have hT : ∀ p, p.Prime → p ∣ choose n k → p ≤ min k (n / 3) := by
    intro p hp hd
    have hpk := hsmooth p hp hd
    by_contra hlt
    have h3 : n < 3 * p := by omega
    have := factorization_choose_of_lt_three_mul (n := n) (k := k) (p := p) (by omega) hpk
      (by omega) h3
    have hpos : 0 < (choose n k).factorization p :=
      hp.factorization_pos_of_dvd (choose_pos (by omega)).ne' hd
    omega
  rw [choose_eq_prod_small n k (min k (n / 3)) (by omega) (by omega) hT]
  set S := {p ∈ range (min k (n / 3) + 1) | p.Prime}
  set f := fun p => p ^ (choose n k).factorization p
  rw [← prod_filter_mul_prod_filter_not S (· ≤ sqrt n)]
  apply Nat.mul_le_mul
  · refine (prod_le_pow_card _ _ n fun p _ => pow_factorization_choose_le (by omega)).trans ?_
    apply Nat.pow_le_pow_right (by omega)
    apply card_le_card
    intro p hp
    simp only [S, mem_filter, mem_range] at hp ⊢
    exact ⟨by omega, hp.1.2⟩
  · refine le_trans ?_ (primorial_le_four_pow (min k (n / 3)))
    refine (prod_le_prod' fun p hp => (?_ : f p ≤ p)).trans ?_
    · simp only [S, mem_filter, mem_range, not_le] at hp
      refine (Nat.pow_le_pow_right hp.1.2.one_lt.le ?_).trans (pow_one p).le
      exact Nat.factorization_choose_le_one (sqrt_lt'.mp hp.2)
    refine prod_le_prod_of_subset_of_one_le' (filter_subset _ _) ?_
    intro p hp _
    simp only [mem_filter] at hp
    exact hp.2.one_lt.le

/-! ### Lower bounds -/

theorem pow_le_pow_mul_choose (n k : ℕ) (hkn : k ≤ n) : n ^ k ≤ k ^ k * choose n k := by
  have h1 : k ! * choose n k = ∏ i ∈ range k, (n - i) := by
    rw [← descFactorial_eq_factorial_mul_choose, descFactorial_eq_prod_range]
  have h2 : k ! = ∏ i ∈ range k, (k - i) := by
    rw [factorial_eq_prod_range_add_one, ← prod_range_reflect]
    apply prod_congr rfl; intro i hi; simp at hi; omega
  have h3 : n ^ k * k ! ≤ k ^ k * (k ! * choose n k) := by
    have en : n ^ k = ∏ _i ∈ range k, n := by simp
    have ek : k ^ k = ∏ _i ∈ range k, k := by simp
    rw [h1, h2, en, ek, ← prod_mul_distrib, ← prod_mul_distrib]
    apply prod_le_prod'; intro i hi; simp at hi
    have : n * (k - i) ≤ k * (n - i) := by
      rw [Nat.mul_sub, Nat.mul_sub]
      have : k * i ≤ n * i := Nat.mul_le_mul_right _ hkn
      have : n * i ≤ n * k := Nat.mul_le_mul_left _ hi.le
      rw [mul_comm k n]; omega
    exact this
  have hpos : 0 < k ! := factorial_pos k
  have : n ^ k * k ! ≤ (k ^ k * choose n k) * k ! := by linarith [h3]
  exact Nat.le_of_mul_le_mul_right this hpos

theorem choose_mono_half (n a : ℕ) :
    ∀ b, a ≤ b → b ≤ n / 2 → choose n a ≤ choose n b := by
  intro b hab hb
  induction b, hab using Nat.le_induction with
  | base => exact le_rfl
  | succ b hab ih => exact (ih (by omega)).trans (Nat.choose_le_succ_of_lt_half_left (by omega))

theorem four_mul_choose_le_succ (n j : ℕ) (h : 5 * j + 4 ≤ n) :
    4 * choose n j ≤ choose n (j + 1) := by
  have e := Nat.choose_succ_right_eq n j
  have : 4 * choose n j * (j + 1) ≤ choose n (j + 1) * (j + 1) := by
    rw [e]; have : 4 * (j + 1) ≤ n - j := by omega
    nlinarith
  exact Nat.le_of_mul_le_mul_right this (by omega)

theorem choose_succ_le_four_mul (n j : ℕ) (h : n ≤ 5 * j + 4) :
    choose n (j + 1) ≤ 4 * choose n j := by
  have e := Nat.choose_succ_right_eq n j
  have : choose n (j + 1) * (j + 1) ≤ 4 * choose n j * (j + 1) := by
    rw [e]; have : n - j ≤ 4 * (j + 1) := by omega
    nlinarith
  exact Nat.le_of_mul_le_mul_right this (by omega)

theorem four_pow_mul_choose_le (n K : ℕ) : ∀ k, K ≤ k → 5 * k ≤ n + 1 →
    4 ^ (k - K) * choose n K ≤ choose n k := by
  intro k hk
  induction k, hk using Nat.le_induction with
  | base => intro _; simp
  | succ k hk ih =>
    intro h5
    have := ih (by omega)
    have h4 := four_mul_choose_le_succ n k (by omega)
    rw [show k + 1 - K = (k - K) + 1 by omega, pow_succ]
    nlinarith

theorem choose_le_four_pow_mul (n k : ℕ) (hk : n ≤ 5 * k + 4) : ∀ m, k ≤ m →
    choose n m ≤ 4 ^ (m - k) * choose n k := by
  intro m hm
  induction m, hm using Nat.le_induction with
  | base => simp
  | succ m hm ih =>
    have h4 := choose_succ_le_four_mul n m (by omega)
    rw [show m + 1 - k = (m - k) + 1 by omega, pow_succ]
    nlinarith

theorem six_pow_le_choose (m : ℕ) (hm : 20 ≤ m) : 6 ^ m ≤ choose (3 * m) m := by
  induction m, hm using Nat.le_induction with
  | base =>
    rw [Nat.choose_eq_factorial_div_factorial (by norm_num)]
    norm_num [Nat.factorial]
  | succ m hm ih =>
    have e1 := Nat.choose_mul_succ_eq (3 * m) m
    have e2 := Nat.choose_mul_succ_eq (3 * m + 1) m
    have e3 := Nat.add_one_mul_choose_eq (3 * m + 2) m
    rw [show 3 * m + 1 - m = 2 * m + 1 by omega] at e1
    rw [show 3 * m + 1 + 1 - m = 2 * m + 2 by omega, show 3 * m + 1 + 1 = 3 * m + 2 by ring] at e2
    rw [show 3 * (m + 1) = 3 * m + 2 + 1 by ring, pow_succ]
    have eD : choose (3 * m + 2 + 1) (m + 1) * ((m + 1) * (2 * m + 2) * (2 * m + 1)) =
        choose (3 * m) m * ((3 * m + 1) * (3 * m + 2) * (3 * m + 3)) := by
      calc choose (3 * m + 2 + 1) (m + 1) * ((m + 1) * (2 * m + 2) * (2 * m + 1))
          = (choose (3 * m + 2 + 1) (m + 1) * (m + 1)) * (2 * m + 2) * (2 * m + 1) := by ring
        _ = (3 * m + 2 + 1) * (choose (3 * m + 2) m * (2 * m + 2)) * (2 * m + 1) := by
            rw [← e3]; ring
        _ = (3 * m + 2 + 1) * (3 * m + 2) * (choose (3 * m + 1) m * (2 * m + 1)) := by
            rw [← e2]; ring
        _ = _ := by rw [← e1]; ring
    have hpoly : 6 * ((m + 1) * (2 * m + 2) * (2 * m + 1)) ≤
        (3 * m + 1) * (3 * m + 2) * (3 * m + 3) := by
      have h1 : 20 * (m * m) ≤ m * (m * m) := Nat.mul_le_mul_right _ hm
      nlinarith
    have key : 6 * choose (3 * m) m * ((m + 1) * (2 * m + 2) * (2 * m + 1)) ≤
        choose (3 * m + 2 + 1) (m + 1) * ((m + 1) * (2 * m + 2) * (2 * m + 1)) := by
      calc 6 * choose (3 * m) m * ((m + 1) * (2 * m + 2) * (2 * m + 1))
          = choose (3 * m) m * (6 * ((m + 1) * (2 * m + 2) * (2 * m + 1))) := by ring
        _ ≤ choose (3 * m) m * ((3 * m + 1) * (3 * m + 2) * (3 * m + 3)) :=
            Nat.mul_le_mul_left _ hpoly
        _ = _ := eD.symm
    have := Nat.le_of_mul_le_mul_right key (by positivity)
    nlinarith

/-! ### Counting primes -/

theorem numPrimes_eq (x : ℕ) : numPrimes x = primeCounting' (x + 1) := by
  rw [numPrimes, primeCounting', count_eq_card_filter_range]

theorem numPrimes_le (x : ℕ) : 3 * numPrimes x ≤ x + 12 := by
  rcases lt_or_ge x 6 with hx | hx
  · interval_cases x <;> decide
  · have h := primeCounting'_add_le (a := 6) (k := 7) (by norm_num) (by norm_num) (x - 6)
    have ht : Nat.totient 6 = 2 := by decide
    have h7 : primeCounting' 7 = 3 := by decide
    rw [ht, h7, show 7 + (x - 6) = x + 1 by omega] at h
    rw [numPrimes_eq]
    omega

theorem numPrimes_le_self (x : ℕ) : numPrimes x ≤ x := by
  unfold numPrimes
  calc #{p ∈ range (x + 1) | p.Prime} ≤ #(Ioc 0 x) := by
        apply card_le_card; intro p hp
        simp only [mem_filter, mem_range, mem_Ioc] at hp ⊢
        exact ⟨hp.2.pos, by omega⟩
    _ = x := by simp

/-! ### Numerical inequalities -/

theorem small_table : ∀ k < 64, 0 < k → k ^ k < 4096 ^ (k - numPrimes k) := by
  decide +kernel

theorem regimeA (n k : ℕ) (hn : 4096 ≤ n) (hk : 0 < k) (hkn : k * k ≤ 4 * n) :
    k ^ k < n ^ (k - numPrimes k) := by
  rcases lt_or_ge k 64 with hk2 | hk2
  · exact (small_table k hk2 hk).trans_le (Nat.pow_le_pow_left hn _)
  · set d := k - numPrimes k with hd
    have h3 := numPrimes_le k
    have hle := numPrimes_le_self k
    have hd3 : 3 * d + 12 ≥ 2 * k := by omega
    have h1 : k ^ (2 * d) ≤ 4 ^ d * n ^ d := by
      rw [pow_mul, ← mul_pow]
      exact Nat.pow_le_pow_left (by nlinarith) _
    have h2 : 4 ^ d < k ^ (2 * d - k) := by
      calc 4 ^ d = 2 ^ (2 * d) := by rw [pow_mul]; norm_num
        _ < 2 ^ (6 * (2 * d - k)) := Nat.pow_lt_pow_right (by norm_num) (by omega)
        _ = 64 ^ (2 * d - k) := by rw [pow_mul]; norm_num
        _ ≤ k ^ (2 * d - k) := Nat.pow_le_pow_left hk2 _
    have e : k ^ (2 * d) = k ^ k * k ^ (2 * d - k) := by
      rw [← pow_add]; congr 1; omega
    have hkk : 0 < k ^ k := by positivity
    have : 4 ^ d * k ^ k < 4 ^ d * n ^ d := by
      calc 4 ^ d * k ^ k < k ^ (2 * d - k) * k ^ k := Nat.mul_lt_mul_of_pos_right h2 hkk
        _ = k ^ (2 * d) := by rw [e]; ring
        _ ≤ _ := h1
    exact Nat.lt_of_mul_lt_mul_left this

theorem ineqE1 (n : ℕ) (hn : 4096 ≤ n) :
    4 ^ (2 * sqrt n) * n ^ numPrimes (sqrt n) < choose n (2 * sqrt n) := by
  set s := sqrt n with hs_def
  set e := numPrimes s
  have hs : 64 ≤ s := by rw [hs_def, Nat.le_sqrt]; omega
  have hsq : s * s ≤ n := Nat.sqrt_le n
  have hsq' : n < (s + 1) * (s + 1) := Nat.lt_succ_sqrt n
  have he := numPrimes_le s
  have h14 : 14 * e < 6 * s := by omega
  have hlow := pow_le_pow_mul_choose n (2 * s) (by nlinarith)
  have hn1 : s ^ (4 * s) ≤ n ^ (2 * s) := by
    rw [show 4 * s = 2 * (2 * s) by ring, pow_mul, sq]
    exact Nat.pow_le_pow_left hsq _
  have hn2 : n ^ e ≤ 4 ^ e * s ^ (2 * e) := by
    rw [pow_mul, ← mul_pow]
    exact Nat.pow_le_pow_left (by nlinarith) _
  have h2 : 2 ^ (6 * s + 2 * e) < s ^ (2 * s - 2 * e) := by
    calc 2 ^ (6 * s + 2 * e) < 2 ^ (6 * (2 * s - 2 * e)) :=
          Nat.pow_lt_pow_right (by norm_num) (by omega)
      _ = 64 ^ (2 * s - 2 * e) := by rw [pow_mul]; norm_num
      _ ≤ s ^ (2 * s - 2 * e) := Nat.pow_le_pow_left hs _
  have key : 4 ^ (2 * s) * n ^ e * (2 * s) ^ (2 * s) < (2 * s) ^ (2 * s) * choose n (2 * s) := by
    calc 4 ^ (2 * s) * n ^ e * (2 * s) ^ (2 * s)
        ≤ 4 ^ (2 * s) * (4 ^ e * s ^ (2 * e)) * (2 * s) ^ (2 * s) := by gcongr
      _ = 2 ^ (6 * s + 2 * e) * s ^ (2 * s + 2 * e) := by
          have h1 : (4:ℕ) ^ (2 * s) = 2 ^ (4 * s) := by
            rw [show (4:ℕ) = 2 ^ 2 by norm_num, ← pow_mul]; ring_nf
          have h2 : (4:ℕ) ^ e = 2 ^ (2 * e) := by
            rw [show (4:ℕ) = 2 ^ 2 by norm_num, ← pow_mul]
          rw [h1, h2, mul_pow, pow_add, pow_add, show 6 * s = 4 * s + 2 * s by ring, pow_add]
          ring
      _ < s ^ (2 * s - 2 * e) * s ^ (2 * s + 2 * e) :=
          Nat.mul_lt_mul_of_pos_right h2 (by positivity)
      _ = s ^ (4 * s) := by rw [← pow_add]; congr 1; omega
      _ ≤ n ^ (2 * s) := hn1
      _ ≤ _ := hlow
  rw [mul_comm ((2 * s) ^ (2 * s))] at key
  exact Nat.lt_of_mul_lt_mul_right key

theorem ineqE2 (n : ℕ) (hn : 4096 ≤ n) :
    4 ^ (n / 3) * n ^ numPrimes (sqrt n) < choose n (n / 3) := by
  set s := sqrt n with hs_def
  set e := numPrimes s
  set m := n / 3 with hm_def
  have hs : 64 ≤ s := by rw [hs_def, Nat.le_sqrt]; omega
  have hsq : s * s ≤ n := Nat.sqrt_le n
  have hsq' : n < (s + 1) * (s + 1) := Nat.lt_succ_sqrt n
  have he := numPrimes_le s
  set u := s / 8 with hu
  have hu8 : 8 ≤ u := by omega
  have hsu : s + 1 ≤ 2 ^ (u + 3) := by
    have := Nat.lt_two_pow_self (n := u)
    rw [pow_add]; omega
  have hn2 : n ^ e ≤ 2 ^ ((2 * u + 6) * e) := by
    rw [pow_mul]
    apply Nat.pow_le_pow_left
    calc n ≤ (s + 1) * (s + 1) := hsq'.le
      _ ≤ 2 ^ (u + 3) * 2 ^ (u + 3) := Nat.mul_le_mul hsu hsu
      _ = 2 ^ (2 * u + 6) := by rw [← pow_add]; ring_nf
  have hexp : (2 * u + 6) * e + 1 < m / 2 := by
    have h1 : (2 * u + 6) * (3 * e) ≤ (2 * u + 6) * (8 * u + 19) :=
      Nat.mul_le_mul_left _ (by omega)
    have h2 : (8 * u) * (8 * u) ≤ s * s := Nat.mul_le_mul (by omega) (by omega)
    have h3 : 3 * m + 2 ≥ n := by omega
    have h4 : 2 * (m / 2) + 1 ≥ m := by omega
    nlinarith
  have hlow : 6 ^ m ≤ choose n m :=
    (six_pow_le_choose m (by omega)).trans (Nat.choose_le_choose _ (by omega))
  have h3m : 2 ^ (3 * (m / 2)) ≤ 3 ^ m := by
    calc 2 ^ (3 * (m / 2)) = 8 ^ (m / 2) := by rw [pow_mul]; norm_num
      _ ≤ 9 ^ (m / 2) := Nat.pow_le_pow_left (by norm_num) _
      _ = 3 ^ (2 * (m / 2)) := by rw [pow_mul]; norm_num
      _ ≤ 3 ^ m := Nat.pow_le_pow_right (by norm_num) (by omega)
  have h2m : 2 ^ m * n ^ e < 3 ^ m := by
    calc 2 ^ m * n ^ e ≤ 2 ^ m * 2 ^ ((2 * u + 6) * e) := Nat.mul_le_mul_left _ hn2
      _ = 2 ^ (m + (2 * u + 6) * e) := by rw [← pow_add]
      _ < 2 ^ (3 * (m / 2)) := Nat.pow_lt_pow_right (by norm_num) (by omega)
      _ ≤ 3 ^ m := h3m
  calc 4 ^ m * n ^ e = 2 ^ m * (2 ^ m * n ^ e) := by
        rw [show (4:ℕ) = 2 * 2 by norm_num, mul_pow]; ring
    _ < 2 ^ m * 3 ^ m := Nat.mul_lt_mul_of_pos_left h2m (by positivity)
    _ = 6 ^ m := by rw [← mul_pow]; norm_num
    _ ≤ _ := hlow

/-! ### Sylvester's theorem -/

theorem exists_prime_gt_dvd_choose (k n : ℕ) (h : 2 * k ≤ n) (hk : 0 < k) :
    ∃ p, k < p ∧ p.Prime ∧ p ∣ choose n k := by
  by_contra hcon
  push_neg at hcon
  have hsmooth : ∀ p, p.Prime → p ∣ choose n k → p ≤ k := fun p hp hd => by
    by_contra hlt
    exact hcon p (by omega) hp hd
  rcases lt_or_ge n 4096 with hn | hn
  · obtain ⟨p, hp, hkp, hmod⟩ := small_n n hn k hk h
    exact absurd (hsmooth p hp (prime_dvd_choose_of_mod_lt hp hkp hmod)) (by omega)
  have hs : 64 ≤ sqrt n := by
    rw [Nat.le_sqrt]; omega
  have hsq : sqrt n * sqrt n ≤ n := Nat.sqrt_le n
  rcases le_or_gt k (2 * sqrt n) with hk2 | hk2
  · -- regime A
    have h1 := choose_le_pow_numPrimes n k (by omega) hsmooth
    have h2 := pow_le_pow_mul_choose n k (by omega)
    have h3 := regimeA n k hn hk (by nlinarith)
    have hle := numPrimes_le_self k
    have hn0 : 0 < n := by omega
    have : n ^ k ≤ k ^ k * n ^ numPrimes k := h2.trans (Nat.mul_le_mul_left _ h1)
    have e : n ^ k = n ^ (k - numPrimes k) * n ^ numPrimes k := by
      rw [← pow_add]; congr 1; omega
    rw [e] at this
    have := Nat.le_of_mul_le_mul_right this (by positivity)
    omega
  · have hU := choose_le_of_smooth n k (by omega) h hsmooth
    rcases le_or_gt (5 * k) (n + 1) with h5 | h5
    · have hc := four_pow_mul_choose_le n (2 * sqrt n) k hk2.le h5
      have hE := ineqE1 n hn
      have hmin : min k (n / 3) ≤ k := min_le_left _ _
      have : n ^ numPrimes (sqrt n) * 4 ^ min k (n / 3) ≤ n ^ numPrimes (sqrt n) * 4 ^ k :=
        Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by norm_num) hmin)
      have e : 4 ^ k = 4 ^ (k - 2 * sqrt n) * 4 ^ (2 * sqrt n) := by
        rw [← pow_add]; congr 1; omega
      have hpos : 0 < 4 ^ (k - 2 * sqrt n) := by positivity
      have h4 : 4 ^ (k - 2 * sqrt n) * (4 ^ (2 * sqrt n) * n ^ numPrimes (sqrt n)) <
          4 ^ (k - 2 * sqrt n) * choose n (2 * sqrt n) := Nat.mul_lt_mul_of_pos_left hE hpos
      have : choose n k < choose n k :=
        calc choose n k ≤ n ^ numPrimes (sqrt n) * 4 ^ k := hU.trans this
          _ = 4 ^ (k - 2 * sqrt n) * (4 ^ (2 * sqrt n) * n ^ numPrimes (sqrt n)) := by
            rw [e]; ring
          _ < 4 ^ (k - 2 * sqrt n) * choose n (2 * sqrt n) := h4
          _ ≤ choose n k := hc
      exact lt_irrefl _ this
    · rcases le_or_gt k (n / 3) with h3 | h3
      · have hc := choose_le_four_pow_mul n k (by omega) (n / 3) h3
        have hE := ineqE2 n hn
        have hmin : min k (n / 3) = k := min_eq_left h3
        rw [hmin] at hU
        have e : 4 ^ (n / 3) = 4 ^ (n / 3 - k) * 4 ^ k := by
          rw [← pow_add]; congr 1; omega
        have h4 : 4 ^ (n / 3 - k) * (4 ^ k * n ^ numPrimes (sqrt n)) <
            4 ^ (n / 3 - k) * choose n k :=
          calc 4 ^ (n / 3 - k) * (4 ^ k * n ^ numPrimes (sqrt n))
              = 4 ^ (n / 3) * n ^ numPrimes (sqrt n) := by rw [e]; ring
            _ < choose n (n / 3) := hE
            _ ≤ 4 ^ (n / 3 - k) * choose n k := hc
        have h5 := Nat.lt_of_mul_lt_mul_left h4
        have : choose n k < choose n k :=
          calc choose n k ≤ n ^ numPrimes (sqrt n) * 4 ^ k := hU
            _ = 4 ^ k * n ^ numPrimes (sqrt n) := by ring
            _ < choose n k := h5
        exact lt_irrefl _ this
      · have hmin : min k (n / 3) = n / 3 := min_eq_right h3.le
        rw [hmin] at hU
        have hE := ineqE2 n hn
        have hmono : choose n (n / 3) ≤ choose n k :=
          choose_mono_half n (n / 3) k h3.le (by omega)
        have : choose n k < choose n k :=
          calc choose n k ≤ n ^ numPrimes (sqrt n) * 4 ^ (n / 3) := hU
            _ = 4 ^ (n / 3) * n ^ numPrimes (sqrt n) := by ring
            _ < choose n (n / 3) := hE
            _ ≤ choose n k := hmono
        exact lt_irrefl _ this

end chapter3.Sylvester
