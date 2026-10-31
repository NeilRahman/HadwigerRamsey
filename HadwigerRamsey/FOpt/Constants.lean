import HadwigerRamsey.FOpt.Definitions
import HadwigerRamsey.FOpt.Interval

namespace HadwigerRamsey.FOpt
open Real LeanCert.Core LeanCert.Core.IntervalRat
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

def qI : IntervalRat := ⟨202041028/1000000000,202041030/1000000000,by norm_num⟩
def cI : IntervalRat := ⟨399821/1000000,399822/1000000,by norm_num⟩
def fI : IntervalRat := ⟨293325/1000000,293327/1000000,by norm_num⟩
def aI : IntervalRat := ⟨4544/10000,4545/10000,by norm_num⟩
def log2I : IntervalRat := ⟨693147/1000000,693148/1000000,by norm_num⟩

def encloses (J I : IntervalRat) : Bool := decide (J.lo ≤ I.lo ∧ I.hi ≤ J.hi)
lemma enlarge {x : ℝ} {I J : IntervalRat} (hx : x ∈ I) (h : encloses J I = true) : x ∈ J := by
  have hh : J.lo ≤ I.lo ∧ I.hi ≤ J.hi := by simpa [encloses] using h
  exact ⟨le_trans (by exact_mod_cast hh.1) hx.1, le_trans hx.2 (by exact_mod_cast hh.2)⟩

lemma q_mem : q ∈ qI := by simpa [qI,IntervalRat.mem_def] using q_bounds
lemma c_mem : c ∈ cI := by
  have hh := mem_logComputable q_mem (by decide +kernel : 0 < qI.lo) 20
  have hc := mem_scale (-1/4) hh
  have he : (-(1/4) : ℝ)*log q = c := by dsimp [c]; ring
  norm_num only [Rat.cast_div, Rat.cast_neg, Rat.cast_one, Rat.cast_ofNat] at hc
  rw [he] at hc
  exact enlarge hc (by decide +kernel)

lemma log2_mem : log 2 ∈ log2I := by
  have hh := mem_logPointComputable (q := 2) (by norm_num) 20
  norm_num only [Rat.cast_ofNat] at hh
  exact enlarge hh (by decide +kernel)

lemma F_mem : F ∈ fI := enlarge (mem_sub log2_mem c_mem) (by decide +kernel)

lemma a_mem : a ∈ aI := by
  have hd := mem_sub (mem_singleton 2) q_mem
  have hp : 0 < (sub (singleton 2) qI).lo := by decide +kernel
  have hi := mem_invNonzero (I := ⟨sub (singleton 2) qI,
    by simp only [containsZero]; intro hz; exact (not_le.mpr (by decide +kernel : 0 < (sub (singleton 2) qI).lo)) hz.1⟩) hd
    (by have := q_lt_one; norm_num; linarith : (2 : ℝ)-q ≠ 0)
  have hh := mem_sub (mem_scale 4 F_mem) (mem_mul (mem_mul (mem_scale 16 c_mem) q_mem) hi)
  have he : 4*F - (16*c*q)*(2-q)⁻¹ = a := by dsimp [a]; ring
  norm_num only [Rat.cast_ofNat] at hh
  rw [he] at hh
  exact enlarge hh (by decide +kernel)

lemma a_nonneg : 0 ≤ a := le_trans (by norm_num [aI]) a_mem.1

end HadwigerRamsey.FOpt
