import HadwigerRamsey.FOpt.Certificates

set_option maxHeartbeats 1000000

namespace HadwigerRamsey.FOpt
open LeanCert.Core LeanCert.Core.IntervalRat

/-- Coverage of the outer intervals by the checked blocks. -/
theorem gap_checks (j : Fin 1001)
    (hr : 350 ≤ j.val ∧ j.val ≤ 399 ∨ 600 ≤ j.val) :
    gapE.lowerCheck (certificateEnv (cell j.val)) 16 0 = true := by
  have hm : j.val % 10 < 10 := Nat.mod_lt _ (by norm_num)
  have he := Nat.div_add_mod j.val 10
  by_cases hj : j.val = 1000
  · simpa only [hj] using gap_last
  rcases hr with hr | hr
  · have hb : 35 ≤ j.val / 10 ∧ j.val / 10 ≤ 39 := by omega
    obtain ⟨hb0,hb1⟩ := hb
    interval_cases hd : j.val / 10
    · have hj' : j.val = 350 + j.val % 10 := by omega
      rw [hj']
      exact gap_block_35 ⟨j.val % 10,hm⟩
    · have hj' : j.val = 360 + j.val % 10 := by omega
      rw [hj']
      exact gap_block_36 ⟨j.val % 10,hm⟩
    · have hj' : j.val = 370 + j.val % 10 := by omega
      rw [hj']
      exact gap_block_37 ⟨j.val % 10,hm⟩
    · have hj' : j.val = 380 + j.val % 10 := by omega
      rw [hj']
      exact gap_block_38 ⟨j.val % 10,hm⟩
    · have hj' : j.val = 390 + j.val % 10 := by omega
      rw [hj']
      exact gap_block_39 ⟨j.val % 10,hm⟩
  · have hb : 60 ≤ j.val / 10 ∧ j.val / 10 ≤ 99 := by omega
    obtain ⟨hb0,hb1⟩ := hb
    interval_cases hd : j.val / 10
    · have hj' : j.val = 600 + j.val % 10 := by omega
      rw [hj']
      exact gap_block_60 ⟨j.val % 10,hm⟩
    · have hj' : j.val = 610 + j.val % 10 := by omega
      rw [hj']
      exact gap_block_61 ⟨j.val % 10,hm⟩
    · have hj' : j.val = 620 + j.val % 10 := by omega
      rw [hj']
      exact gap_block_62 ⟨j.val % 10,hm⟩
    · have hj' : j.val = 630 + j.val % 10 := by omega
      rw [hj']
      exact gap_block_63 ⟨j.val % 10,hm⟩
    · have hj' : j.val = 640 + j.val % 10 := by omega
      rw [hj']
      exact gap_block_64 ⟨j.val % 10,hm⟩
    · have hj' : j.val = 650 + j.val % 10 := by omega
      rw [hj']
      exact gap_block_65 ⟨j.val % 10,hm⟩
    · have hj' : j.val = 660 + j.val % 10 := by omega
      rw [hj']
      exact gap_block_66 ⟨j.val % 10,hm⟩
    · have hj' : j.val = 670 + j.val % 10 := by omega
      rw [hj']
      exact gap_block_67 ⟨j.val % 10,hm⟩
    · have hj' : j.val = 680 + j.val % 10 := by omega
      rw [hj']
      exact gap_block_68 ⟨j.val % 10,hm⟩
    · have hj' : j.val = 690 + j.val % 10 := by omega
      rw [hj']
      exact gap_block_69 ⟨j.val % 10,hm⟩
    · have hj' : j.val = 700 + j.val % 10 := by omega
      rw [hj']
      exact gap_block_70 ⟨j.val % 10,hm⟩
    · have hj' : j.val = 710 + j.val % 10 := by omega
      rw [hj']
      exact gap_block_71 ⟨j.val % 10,hm⟩
    · have hj' : j.val = 720 + j.val % 10 := by omega
      rw [hj']
      exact gap_block_72 ⟨j.val % 10,hm⟩
    · have hj' : j.val = 730 + j.val % 10 := by omega
      rw [hj']
      exact gap_block_73 ⟨j.val % 10,hm⟩
    · have hj' : j.val = 740 + j.val % 10 := by omega
      rw [hj']
      exact gap_block_74 ⟨j.val % 10,hm⟩
    · have hj' : j.val = 750 + j.val % 10 := by omega
      rw [hj']
      exact gap_block_75 ⟨j.val % 10,hm⟩
    · have hj' : j.val = 760 + j.val % 10 := by omega
      rw [hj']
      exact gap_block_76 ⟨j.val % 10,hm⟩
    · have hj' : j.val = 770 + j.val % 10 := by omega
      rw [hj']
      exact gap_block_77 ⟨j.val % 10,hm⟩
    · have hj' : j.val = 780 + j.val % 10 := by omega
      rw [hj']
      exact gap_block_78 ⟨j.val % 10,hm⟩
    · have hj' : j.val = 790 + j.val % 10 := by omega
      rw [hj']
      exact gap_block_79 ⟨j.val % 10,hm⟩
    · have hj' : j.val = 800 + j.val % 10 := by omega
      rw [hj']
      exact gap_block_80 ⟨j.val % 10,hm⟩
    · have hj' : j.val = 810 + j.val % 10 := by omega
      rw [hj']
      exact gap_block_81 ⟨j.val % 10,hm⟩
    · have hj' : j.val = 820 + j.val % 10 := by omega
      rw [hj']
      exact gap_block_82 ⟨j.val % 10,hm⟩
    · have hj' : j.val = 830 + j.val % 10 := by omega
      rw [hj']
      exact gap_block_83 ⟨j.val % 10,hm⟩
    · have hj' : j.val = 840 + j.val % 10 := by omega
      rw [hj']
      exact gap_block_84 ⟨j.val % 10,hm⟩
    · have hj' : j.val = 850 + j.val % 10 := by omega
      rw [hj']
      exact gap_block_85 ⟨j.val % 10,hm⟩
    · have hj' : j.val = 860 + j.val % 10 := by omega
      rw [hj']
      exact gap_block_86 ⟨j.val % 10,hm⟩
    · have hj' : j.val = 870 + j.val % 10 := by omega
      rw [hj']
      exact gap_block_87 ⟨j.val % 10,hm⟩
    · have hj' : j.val = 880 + j.val % 10 := by omega
      rw [hj']
      exact gap_block_88 ⟨j.val % 10,hm⟩
    · have hj' : j.val = 890 + j.val % 10 := by omega
      rw [hj']
      exact gap_block_89 ⟨j.val % 10,hm⟩
    · have hj' : j.val = 900 + j.val % 10 := by omega
      rw [hj']
      exact gap_block_90 ⟨j.val % 10,hm⟩
    · have hj' : j.val = 910 + j.val % 10 := by omega
      rw [hj']
      exact gap_block_91 ⟨j.val % 10,hm⟩
    · have hj' : j.val = 920 + j.val % 10 := by omega
      rw [hj']
      exact gap_block_92 ⟨j.val % 10,hm⟩
    · have hj' : j.val = 930 + j.val % 10 := by omega
      rw [hj']
      exact gap_block_93 ⟨j.val % 10,hm⟩
    · have hj' : j.val = 940 + j.val % 10 := by omega
      rw [hj']
      exact gap_block_94 ⟨j.val % 10,hm⟩
    · have hj' : j.val = 950 + j.val % 10 := by omega
      rw [hj']
      exact gap_block_95 ⟨j.val % 10,hm⟩
    · have hj' : j.val = 960 + j.val % 10 := by omega
      rw [hj']
      exact gap_block_96 ⟨j.val % 10,hm⟩
    · have hj' : j.val = 970 + j.val % 10 := by omega
      rw [hj']
      exact gap_block_97 ⟨j.val % 10,hm⟩
    · have hj' : j.val = 980 + j.val % 10 := by omega
      rw [hj']
      exact gap_block_98 ⟨j.val % 10,hm⟩
    · have hj' : j.val = 990 + j.val % 10 := by omega
      rw [hj']
      exact gap_block_99 ⟨j.val % 10,hm⟩

/-- Coverage of the convex middle interval by the checked blocks. -/
theorem curvature_checks (j : Fin 601) (hr : 400 ≤ j.val) :
    curvatureE.lowerCheck (certificateEnv (cell j.val)) 16 0 = true := by
  have hm : j.val % 10 < 10 := Nat.mod_lt _ (by norm_num)
  have he := Nat.div_add_mod j.val 10
  by_cases hj : j.val = 600
  · simpa only [hj] using curvature_last
  have hb : 40 ≤ j.val / 10 ∧ j.val / 10 ≤ 59 := by omega
  obtain ⟨hb0,hb1⟩ := hb
  interval_cases hd : j.val / 10
  · have hj' : j.val = 400 + j.val % 10 := by omega
    rw [hj']
    exact curvature_block_40 ⟨j.val % 10,hm⟩
  · have hj' : j.val = 410 + j.val % 10 := by omega
    rw [hj']
    exact curvature_block_41 ⟨j.val % 10,hm⟩
  · have hj' : j.val = 420 + j.val % 10 := by omega
    rw [hj']
    exact curvature_block_42 ⟨j.val % 10,hm⟩
  · have hj' : j.val = 430 + j.val % 10 := by omega
    rw [hj']
    exact curvature_block_43 ⟨j.val % 10,hm⟩
  · have hj' : j.val = 440 + j.val % 10 := by omega
    rw [hj']
    exact curvature_block_44 ⟨j.val % 10,hm⟩
  · have hj' : j.val = 450 + j.val % 10 := by omega
    rw [hj']
    exact curvature_block_45 ⟨j.val % 10,hm⟩
  · have hj' : j.val = 460 + j.val % 10 := by omega
    rw [hj']
    exact curvature_block_46 ⟨j.val % 10,hm⟩
  · have hj' : j.val = 470 + j.val % 10 := by omega
    rw [hj']
    exact curvature_block_47 ⟨j.val % 10,hm⟩
  · have hj' : j.val = 480 + j.val % 10 := by omega
    rw [hj']
    exact curvature_block_48 ⟨j.val % 10,hm⟩
  · have hj' : j.val = 490 + j.val % 10 := by omega
    rw [hj']
    exact curvature_block_49 ⟨j.val % 10,hm⟩
  · have hj' : j.val = 500 + j.val % 10 := by omega
    rw [hj']
    exact curvature_block_50 ⟨j.val % 10,hm⟩
  · have hj' : j.val = 510 + j.val % 10 := by omega
    rw [hj']
    exact curvature_block_51 ⟨j.val % 10,hm⟩
  · have hj' : j.val = 520 + j.val % 10 := by omega
    rw [hj']
    exact curvature_block_52 ⟨j.val % 10,hm⟩
  · have hj' : j.val = 530 + j.val % 10 := by omega
    rw [hj']
    exact curvature_block_53 ⟨j.val % 10,hm⟩
  · have hj' : j.val = 540 + j.val % 10 := by omega
    rw [hj']
    exact curvature_block_54 ⟨j.val % 10,hm⟩
  · have hj' : j.val = 550 + j.val % 10 := by omega
    rw [hj']
    exact curvature_block_55 ⟨j.val % 10,hm⟩
  · have hj' : j.val = 560 + j.val % 10 := by omega
    rw [hj']
    exact curvature_block_56 ⟨j.val % 10,hm⟩
  · have hj' : j.val = 570 + j.val % 10 := by omega
    rw [hj']
    exact curvature_block_57 ⟨j.val % 10,hm⟩
  · have hj' : j.val = 580 + j.val % 10 := by omega
    rw [hj']
    exact curvature_block_58 ⟨j.val % 10,hm⟩
  · have hj' : j.val = 590 + j.val % 10 := by omega
    rw [hj']
    exact curvature_block_59 ⟨j.val % 10,hm⟩

end HadwigerRamsey.FOpt
