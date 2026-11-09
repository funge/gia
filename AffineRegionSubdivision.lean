import AffineRegionSearch

namespace GeneralizedIntervalArithmetic

def HasAffineRegionRoot (X Y : QInterval) (gs cs : List RationalAffineForm) : Prop :=
  ∃ x y, X.Contains x ∧ Y.Contains y ∧ affineRegion cs x y ∧
    Value x y (affineReciprocalSum gs) 0

/-- The same external region is retained in both closed children. -/
theorem affine_region_root_split_x (X Y : QInterval) (gs cs : List RationalAffineForm) :
    HasAffineRegionRoot X Y gs cs ↔
      HasAffineRegionRoot X.lowerHalf Y gs cs ∨ HasAffineRegionRoot X.upperHalf Y gs cs := by
  constructor
  · rintro ⟨x,y,hx,hy,hE,hv⟩
    rcases (split_cover X x).mp hx with hl | hr
    · exact Or.inl ⟨x,y,hl,hy,hE,hv⟩
    · exact Or.inr ⟨x,y,hr,hy,hE,hv⟩
  · rintro (⟨x,y,hx,hy,hE,hv⟩ | ⟨x,y,hx,hy,hE,hv⟩)
    · exact ⟨x,y,lowerHalf_subset hx,hy,hE,hv⟩
    · exact ⟨x,y,upperHalf_subset hx,hy,hE,hv⟩

theorem affine_region_root_split_y (X Y : QInterval) (gs cs : List RationalAffineForm) :
    HasAffineRegionRoot X Y gs cs ↔
      HasAffineRegionRoot X Y.lowerHalf gs cs ∨ HasAffineRegionRoot X Y.upperHalf gs cs := by
  constructor
  · rintro ⟨x,y,hx,hy,hE,hv⟩
    rcases (split_cover Y y).mp hy with hl | hr
    · exact Or.inl ⟨x,y,hx,hl,hE,hv⟩
    · exact Or.inr ⟨x,y,hx,hr,hE,hv⟩
  · rintro (⟨x,y,hx,hy,hE,hv⟩ | ⟨x,y,hx,hy,hE,hv⟩)
    · exact ⟨x,y,hx,lowerHalf_subset hy,hE,hv⟩
    · exact ⟨x,y,hx,upperHalf_subset hy,hE,hv⟩

/-- Reuse the ordinary subdivision engine with the constrained checker. Depth
zero still checks the box; inconclusive leaves stay unknown. -/
def refineAffineRegionBox (depth : Nat) (B : Backend) (X Y : QInterval)
    (gs cs : List RationalAffineForm) : BoxResult :=
  refineBoxes (fun X Y => classifyAffineRegionBox B X Y gs cs) depth .x X Y

theorem refineAffineRegionBox_sound {B : Backend} (hB : BackendSound B)
    (depth : Nat) (X Y : QInterval) (gs cs : List RationalAffineForm) :
    ResultSound (refineAffineRegionBox depth B X Y gs cs) (HasAffineRegionRoot X Y gs cs) :=
  refineBoxes_sound (fun X Y => affine_region_box_sound hB X Y gs cs)
    (fun X Y => affine_region_root_split_x X Y gs cs)
    (fun X Y => affine_region_root_split_y X Y gs cs) depth .x X Y

theorem refineAffineRegionBox_zero (B : Backend) (X Y : QInterval)
    (gs cs : List RationalAffineForm) :
    refineAffineRegionBox 0 B X Y gs cs = classifyAffineRegionBox B X Y gs cs := rfl

end GeneralizedIntervalArithmetic
