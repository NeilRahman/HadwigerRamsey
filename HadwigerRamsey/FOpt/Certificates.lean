import HadwigerRamsey.FOpt.Interval

namespace HadwigerRamsey.FOpt
open LeanCert.Core LeanCert.Core.IntervalRat

namespace RExpr
instance (n : ℕ) : OfNat RExpr n := ⟨.const n⟩
instance : Add RExpr := ⟨.add⟩
instance : Mul RExpr := ⟨.mul⟩
instance : Neg RExpr := ⟨.neg⟩
instance : Sub RExpr := ⟨fun a b => a + -b⟩
instance : Inv RExpr := ⟨.inv⟩
instance : Div RExpr := ⟨fun a b => a * b⁻¹⟩
end RExpr

def xE : RExpr := .var 0
def cE : RExpr := .var 1
def fE : RExpr := .var 2
def aE : RExpr := .var 3
def tE : RExpr := cE / (xE*xE)
def eE : RExpr := .exp (-tE)
def dE : RExpr := 2-eE
def gapE : RExpr := fE*xE + aE*xE*(xE-RExpr.const (1/2))*(1-xE) - xE*xE*RExpr.log dE
def curvatureE : RExpr := aE*(3-6*xE) -
  (2*RExpr.log dE - 2*tE*eE/dE - 8*tE*tE*eE/(dE*dE))

def certificateEnv (I : IntervalRat) : ℕ → IntervalRat
  | 0 => I
  | 1 => ⟨399821/1000000,399822/1000000,by norm_num⟩
  | 2 => ⟨293325/1000000,293327/1000000,by norm_num⟩
  | 3 => ⟨4544/10000,4545/10000,by norm_num⟩
  | _ => singleton 0

def cell (j : ℕ) : IntervalRat := ⟨j/1000,(j+1)/1000,by push_cast; linarith⟩

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

/-- Ten whole-cell checks, each independently reduced by the kernel. -/
theorem gap_block_35 (j : Fin 10) :
    gapE.lowerCheck (certificateEnv (cell (350+j.val))) 16 0 = true := by
  fin_cases j <;> decide +kernel

/-- Ten whole-cell checks, each independently reduced by the kernel. -/
theorem gap_block_36 (j : Fin 10) :
    gapE.lowerCheck (certificateEnv (cell (360+j.val))) 16 0 = true := by
  fin_cases j <;> decide +kernel

/-- Ten whole-cell checks, each independently reduced by the kernel. -/
theorem gap_block_37 (j : Fin 10) :
    gapE.lowerCheck (certificateEnv (cell (370+j.val))) 16 0 = true := by
  fin_cases j <;> decide +kernel

/-- Ten whole-cell checks, each independently reduced by the kernel. -/
theorem gap_block_38 (j : Fin 10) :
    gapE.lowerCheck (certificateEnv (cell (380+j.val))) 16 0 = true := by
  fin_cases j <;> decide +kernel

/-- Ten whole-cell checks, each independently reduced by the kernel. -/
theorem gap_block_39 (j : Fin 10) :
    gapE.lowerCheck (certificateEnv (cell (390+j.val))) 16 0 = true := by
  fin_cases j <;> decide +kernel

/-- Ten whole-cell checks, each independently reduced by the kernel. -/
theorem gap_block_60 (j : Fin 10) :
    gapE.lowerCheck (certificateEnv (cell (600+j.val))) 16 0 = true := by
  fin_cases j <;> decide +kernel

/-- Ten whole-cell checks, each independently reduced by the kernel. -/
theorem gap_block_61 (j : Fin 10) :
    gapE.lowerCheck (certificateEnv (cell (610+j.val))) 16 0 = true := by
  fin_cases j <;> decide +kernel

/-- Ten whole-cell checks, each independently reduced by the kernel. -/
theorem gap_block_62 (j : Fin 10) :
    gapE.lowerCheck (certificateEnv (cell (620+j.val))) 16 0 = true := by
  fin_cases j <;> decide +kernel

/-- Ten whole-cell checks, each independently reduced by the kernel. -/
theorem gap_block_63 (j : Fin 10) :
    gapE.lowerCheck (certificateEnv (cell (630+j.val))) 16 0 = true := by
  fin_cases j <;> decide +kernel

/-- Ten whole-cell checks, each independently reduced by the kernel. -/
theorem gap_block_64 (j : Fin 10) :
    gapE.lowerCheck (certificateEnv (cell (640+j.val))) 16 0 = true := by
  fin_cases j <;> decide +kernel

/-- Ten whole-cell checks, each independently reduced by the kernel. -/
theorem gap_block_65 (j : Fin 10) :
    gapE.lowerCheck (certificateEnv (cell (650+j.val))) 16 0 = true := by
  fin_cases j <;> decide +kernel

/-- Ten whole-cell checks, each independently reduced by the kernel. -/
theorem gap_block_66 (j : Fin 10) :
    gapE.lowerCheck (certificateEnv (cell (660+j.val))) 16 0 = true := by
  fin_cases j <;> decide +kernel

/-- Ten whole-cell checks, each independently reduced by the kernel. -/
theorem gap_block_67 (j : Fin 10) :
    gapE.lowerCheck (certificateEnv (cell (670+j.val))) 16 0 = true := by
  fin_cases j <;> decide +kernel

/-- Ten whole-cell checks, each independently reduced by the kernel. -/
theorem gap_block_68 (j : Fin 10) :
    gapE.lowerCheck (certificateEnv (cell (680+j.val))) 16 0 = true := by
  fin_cases j <;> decide +kernel

/-- Ten whole-cell checks, each independently reduced by the kernel. -/
theorem gap_block_69 (j : Fin 10) :
    gapE.lowerCheck (certificateEnv (cell (690+j.val))) 16 0 = true := by
  fin_cases j <;> decide +kernel

/-- Ten whole-cell checks, each independently reduced by the kernel. -/
theorem gap_block_70 (j : Fin 10) :
    gapE.lowerCheck (certificateEnv (cell (700+j.val))) 16 0 = true := by
  fin_cases j <;> decide +kernel

/-- Ten whole-cell checks, each independently reduced by the kernel. -/
theorem gap_block_71 (j : Fin 10) :
    gapE.lowerCheck (certificateEnv (cell (710+j.val))) 16 0 = true := by
  fin_cases j <;> decide +kernel

/-- Ten whole-cell checks, each independently reduced by the kernel. -/
theorem gap_block_72 (j : Fin 10) :
    gapE.lowerCheck (certificateEnv (cell (720+j.val))) 16 0 = true := by
  fin_cases j <;> decide +kernel

/-- Ten whole-cell checks, each independently reduced by the kernel. -/
theorem gap_block_73 (j : Fin 10) :
    gapE.lowerCheck (certificateEnv (cell (730+j.val))) 16 0 = true := by
  fin_cases j <;> decide +kernel

/-- Ten whole-cell checks, each independently reduced by the kernel. -/
theorem gap_block_74 (j : Fin 10) :
    gapE.lowerCheck (certificateEnv (cell (740+j.val))) 16 0 = true := by
  fin_cases j <;> decide +kernel

/-- Ten whole-cell checks, each independently reduced by the kernel. -/
theorem gap_block_75 (j : Fin 10) :
    gapE.lowerCheck (certificateEnv (cell (750+j.val))) 16 0 = true := by
  fin_cases j <;> decide +kernel

/-- Ten whole-cell checks, each independently reduced by the kernel. -/
theorem gap_block_76 (j : Fin 10) :
    gapE.lowerCheck (certificateEnv (cell (760+j.val))) 16 0 = true := by
  fin_cases j <;> decide +kernel

/-- Ten whole-cell checks, each independently reduced by the kernel. -/
theorem gap_block_77 (j : Fin 10) :
    gapE.lowerCheck (certificateEnv (cell (770+j.val))) 16 0 = true := by
  fin_cases j <;> decide +kernel

/-- Ten whole-cell checks, each independently reduced by the kernel. -/
theorem gap_block_78 (j : Fin 10) :
    gapE.lowerCheck (certificateEnv (cell (780+j.val))) 16 0 = true := by
  fin_cases j <;> decide +kernel

/-- Ten whole-cell checks, each independently reduced by the kernel. -/
theorem gap_block_79 (j : Fin 10) :
    gapE.lowerCheck (certificateEnv (cell (790+j.val))) 16 0 = true := by
  fin_cases j <;> decide +kernel

/-- Ten whole-cell checks, each independently reduced by the kernel. -/
theorem gap_block_80 (j : Fin 10) :
    gapE.lowerCheck (certificateEnv (cell (800+j.val))) 16 0 = true := by
  fin_cases j <;> decide +kernel

/-- Ten whole-cell checks, each independently reduced by the kernel. -/
theorem gap_block_81 (j : Fin 10) :
    gapE.lowerCheck (certificateEnv (cell (810+j.val))) 16 0 = true := by
  fin_cases j <;> decide +kernel

/-- Ten whole-cell checks, each independently reduced by the kernel. -/
theorem gap_block_82 (j : Fin 10) :
    gapE.lowerCheck (certificateEnv (cell (820+j.val))) 16 0 = true := by
  fin_cases j <;> decide +kernel

/-- Ten whole-cell checks, each independently reduced by the kernel. -/
theorem gap_block_83 (j : Fin 10) :
    gapE.lowerCheck (certificateEnv (cell (830+j.val))) 16 0 = true := by
  fin_cases j <;> decide +kernel

/-- Ten whole-cell checks, each independently reduced by the kernel. -/
theorem gap_block_84 (j : Fin 10) :
    gapE.lowerCheck (certificateEnv (cell (840+j.val))) 16 0 = true := by
  fin_cases j <;> decide +kernel

/-- Ten whole-cell checks, each independently reduced by the kernel. -/
theorem gap_block_85 (j : Fin 10) :
    gapE.lowerCheck (certificateEnv (cell (850+j.val))) 16 0 = true := by
  fin_cases j <;> decide +kernel

/-- Ten whole-cell checks, each independently reduced by the kernel. -/
theorem gap_block_86 (j : Fin 10) :
    gapE.lowerCheck (certificateEnv (cell (860+j.val))) 16 0 = true := by
  fin_cases j <;> decide +kernel

/-- Ten whole-cell checks, each independently reduced by the kernel. -/
theorem gap_block_87 (j : Fin 10) :
    gapE.lowerCheck (certificateEnv (cell (870+j.val))) 16 0 = true := by
  fin_cases j <;> decide +kernel

/-- Ten whole-cell checks, each independently reduced by the kernel. -/
theorem gap_block_88 (j : Fin 10) :
    gapE.lowerCheck (certificateEnv (cell (880+j.val))) 16 0 = true := by
  fin_cases j <;> decide +kernel

/-- Ten whole-cell checks, each independently reduced by the kernel. -/
theorem gap_block_89 (j : Fin 10) :
    gapE.lowerCheck (certificateEnv (cell (890+j.val))) 16 0 = true := by
  fin_cases j <;> decide +kernel

/-- Ten whole-cell checks, each independently reduced by the kernel. -/
theorem gap_block_90 (j : Fin 10) :
    gapE.lowerCheck (certificateEnv (cell (900+j.val))) 16 0 = true := by
  fin_cases j <;> decide +kernel

/-- Ten whole-cell checks, each independently reduced by the kernel. -/
theorem gap_block_91 (j : Fin 10) :
    gapE.lowerCheck (certificateEnv (cell (910+j.val))) 16 0 = true := by
  fin_cases j <;> decide +kernel

/-- Ten whole-cell checks, each independently reduced by the kernel. -/
theorem gap_block_92 (j : Fin 10) :
    gapE.lowerCheck (certificateEnv (cell (920+j.val))) 16 0 = true := by
  fin_cases j <;> decide +kernel

/-- Ten whole-cell checks, each independently reduced by the kernel. -/
theorem gap_block_93 (j : Fin 10) :
    gapE.lowerCheck (certificateEnv (cell (930+j.val))) 16 0 = true := by
  fin_cases j <;> decide +kernel

/-- Ten whole-cell checks, each independently reduced by the kernel. -/
theorem gap_block_94 (j : Fin 10) :
    gapE.lowerCheck (certificateEnv (cell (940+j.val))) 16 0 = true := by
  fin_cases j <;> decide +kernel

/-- Ten whole-cell checks, each independently reduced by the kernel. -/
theorem gap_block_95 (j : Fin 10) :
    gapE.lowerCheck (certificateEnv (cell (950+j.val))) 16 0 = true := by
  fin_cases j <;> decide +kernel

/-- Ten whole-cell checks, each independently reduced by the kernel. -/
theorem gap_block_96 (j : Fin 10) :
    gapE.lowerCheck (certificateEnv (cell (960+j.val))) 16 0 = true := by
  fin_cases j <;> decide +kernel

/-- Ten whole-cell checks, each independently reduced by the kernel. -/
theorem gap_block_97 (j : Fin 10) :
    gapE.lowerCheck (certificateEnv (cell (970+j.val))) 16 0 = true := by
  fin_cases j <;> decide +kernel

/-- Ten whole-cell checks, each independently reduced by the kernel. -/
theorem gap_block_98 (j : Fin 10) :
    gapE.lowerCheck (certificateEnv (cell (980+j.val))) 16 0 = true := by
  fin_cases j <;> decide +kernel

/-- Ten whole-cell checks, each independently reduced by the kernel. -/
theorem gap_block_99 (j : Fin 10) :
    gapE.lowerCheck (certificateEnv (cell (990+j.val))) 16 0 = true := by
  fin_cases j <;> decide +kernel

theorem gap_last :
    gapE.lowerCheck (certificateEnv (cell 1000)) 16 0 = true := by
  decide +kernel

/-- Ten whole-cell checks, each independently reduced by the kernel. -/
theorem curvature_block_40 (j : Fin 10) :
    curvatureE.lowerCheck (certificateEnv (cell (400+j.val))) 16 0 = true := by
  fin_cases j <;> decide +kernel

/-- Ten whole-cell checks, each independently reduced by the kernel. -/
theorem curvature_block_41 (j : Fin 10) :
    curvatureE.lowerCheck (certificateEnv (cell (410+j.val))) 16 0 = true := by
  fin_cases j <;> decide +kernel

/-- Ten whole-cell checks, each independently reduced by the kernel. -/
theorem curvature_block_42 (j : Fin 10) :
    curvatureE.lowerCheck (certificateEnv (cell (420+j.val))) 16 0 = true := by
  fin_cases j <;> decide +kernel

/-- Ten whole-cell checks, each independently reduced by the kernel. -/
theorem curvature_block_43 (j : Fin 10) :
    curvatureE.lowerCheck (certificateEnv (cell (430+j.val))) 16 0 = true := by
  fin_cases j <;> decide +kernel

/-- Ten whole-cell checks, each independently reduced by the kernel. -/
theorem curvature_block_44 (j : Fin 10) :
    curvatureE.lowerCheck (certificateEnv (cell (440+j.val))) 16 0 = true := by
  fin_cases j <;> decide +kernel

/-- Ten whole-cell checks, each independently reduced by the kernel. -/
theorem curvature_block_45 (j : Fin 10) :
    curvatureE.lowerCheck (certificateEnv (cell (450+j.val))) 16 0 = true := by
  fin_cases j <;> decide +kernel

/-- Ten whole-cell checks, each independently reduced by the kernel. -/
theorem curvature_block_46 (j : Fin 10) :
    curvatureE.lowerCheck (certificateEnv (cell (460+j.val))) 16 0 = true := by
  fin_cases j <;> decide +kernel

/-- Ten whole-cell checks, each independently reduced by the kernel. -/
theorem curvature_block_47 (j : Fin 10) :
    curvatureE.lowerCheck (certificateEnv (cell (470+j.val))) 16 0 = true := by
  fin_cases j <;> decide +kernel

/-- Ten whole-cell checks, each independently reduced by the kernel. -/
theorem curvature_block_48 (j : Fin 10) :
    curvatureE.lowerCheck (certificateEnv (cell (480+j.val))) 16 0 = true := by
  fin_cases j <;> decide +kernel

/-- Ten whole-cell checks, each independently reduced by the kernel. -/
theorem curvature_block_49 (j : Fin 10) :
    curvatureE.lowerCheck (certificateEnv (cell (490+j.val))) 16 0 = true := by
  fin_cases j <;> decide +kernel

/-- Ten whole-cell checks, each independently reduced by the kernel. -/
theorem curvature_block_50 (j : Fin 10) :
    curvatureE.lowerCheck (certificateEnv (cell (500+j.val))) 16 0 = true := by
  fin_cases j <;> decide +kernel

/-- Ten whole-cell checks, each independently reduced by the kernel. -/
theorem curvature_block_51 (j : Fin 10) :
    curvatureE.lowerCheck (certificateEnv (cell (510+j.val))) 16 0 = true := by
  fin_cases j <;> decide +kernel

/-- Ten whole-cell checks, each independently reduced by the kernel. -/
theorem curvature_block_52 (j : Fin 10) :
    curvatureE.lowerCheck (certificateEnv (cell (520+j.val))) 16 0 = true := by
  fin_cases j <;> decide +kernel

/-- Ten whole-cell checks, each independently reduced by the kernel. -/
theorem curvature_block_53 (j : Fin 10) :
    curvatureE.lowerCheck (certificateEnv (cell (530+j.val))) 16 0 = true := by
  fin_cases j <;> decide +kernel

/-- Ten whole-cell checks, each independently reduced by the kernel. -/
theorem curvature_block_54 (j : Fin 10) :
    curvatureE.lowerCheck (certificateEnv (cell (540+j.val))) 16 0 = true := by
  fin_cases j <;> decide +kernel

/-- Ten whole-cell checks, each independently reduced by the kernel. -/
theorem curvature_block_55 (j : Fin 10) :
    curvatureE.lowerCheck (certificateEnv (cell (550+j.val))) 16 0 = true := by
  fin_cases j <;> decide +kernel

/-- Ten whole-cell checks, each independently reduced by the kernel. -/
theorem curvature_block_56 (j : Fin 10) :
    curvatureE.lowerCheck (certificateEnv (cell (560+j.val))) 16 0 = true := by
  fin_cases j <;> decide +kernel

/-- Ten whole-cell checks, each independently reduced by the kernel. -/
theorem curvature_block_57 (j : Fin 10) :
    curvatureE.lowerCheck (certificateEnv (cell (570+j.val))) 16 0 = true := by
  fin_cases j <;> decide +kernel

/-- Ten whole-cell checks, each independently reduced by the kernel. -/
theorem curvature_block_58 (j : Fin 10) :
    curvatureE.lowerCheck (certificateEnv (cell (580+j.val))) 16 0 = true := by
  fin_cases j <;> decide +kernel

/-- Ten whole-cell checks, each independently reduced by the kernel. -/
theorem curvature_block_59 (j : Fin 10) :
    curvatureE.lowerCheck (certificateEnv (cell (590+j.val))) 16 0 = true := by
  fin_cases j <;> decide +kernel

theorem curvature_last :
    curvatureE.lowerCheck (certificateEnv (cell 600)) 16 0 = true := by
  decide +kernel

end HadwigerRamsey.FOpt
