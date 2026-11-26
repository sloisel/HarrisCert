module

public import HarrisCert.Kernel
public import HarrisCert.Leaves.L10
public import HarrisCert.Leaves.L11
public import HarrisCert.Leaves.L12
public import HarrisCert.Leaves.L13
public import HarrisCert.Leaves.L14
public import HarrisCert.Leaves.L15
public import HarrisCert.Leaves.L16
public import HarrisCert.Leaves.L17
public import HarrisCert.Leaves.L18
public import HarrisCert.Leaves.L19
public import HarrisCert.Leaves.L20
public import HarrisCert.Leaves.L21

/-! Leaves 656 … 1312 cover their boxes. -/

@[expose] public section

namespace Harris

theorem cr_656_657 (k : ℕ) (h1 : 656 ≤ k) (h2 : k < 657) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 656 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf656_ok
theorem cr_657_658 (k : ℕ) (h1 : 657 ≤ k) (h2 : k < 658) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 657 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf657_ok
theorem cr_656_658 (k : ℕ) (h1 : 656 ≤ k) (h2 : k < 658) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 657 then cr_656_657 k h1 h else cr_657_658 k (by omega) h2
theorem cr_658_659 (k : ℕ) (h1 : 658 ≤ k) (h2 : k < 659) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 658 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf658_ok
theorem cr_659_660 (k : ℕ) (h1 : 659 ≤ k) (h2 : k < 660) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 659 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf659_ok
theorem cr_660_661 (k : ℕ) (h1 : 660 ≤ k) (h2 : k < 661) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 660 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf660_ok
theorem cr_659_661 (k : ℕ) (h1 : 659 ≤ k) (h2 : k < 661) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 660 then cr_659_660 k h1 h else cr_660_661 k (by omega) h2
theorem cr_658_661 (k : ℕ) (h1 : 658 ≤ k) (h2 : k < 661) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 659 then cr_658_659 k h1 h else cr_659_661 k (by omega) h2
theorem cr_656_661 (k : ℕ) (h1 : 656 ≤ k) (h2 : k < 661) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 658 then cr_656_658 k h1 h else cr_658_661 k (by omega) h2
theorem cr_661_662 (k : ℕ) (h1 : 661 ≤ k) (h2 : k < 662) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 661 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf661_ok
theorem cr_662_663 (k : ℕ) (h1 : 662 ≤ k) (h2 : k < 663) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 662 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf662_ok
theorem cr_661_663 (k : ℕ) (h1 : 661 ≤ k) (h2 : k < 663) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 662 then cr_661_662 k h1 h else cr_662_663 k (by omega) h2
theorem cr_663_664 (k : ℕ) (h1 : 663 ≤ k) (h2 : k < 664) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 663 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf663_ok
theorem cr_664_665 (k : ℕ) (h1 : 664 ≤ k) (h2 : k < 665) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 664 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf664_ok
theorem cr_665_666 (k : ℕ) (h1 : 665 ≤ k) (h2 : k < 666) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 665 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf665_ok
theorem cr_664_666 (k : ℕ) (h1 : 664 ≤ k) (h2 : k < 666) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 665 then cr_664_665 k h1 h else cr_665_666 k (by omega) h2
theorem cr_663_666 (k : ℕ) (h1 : 663 ≤ k) (h2 : k < 666) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 664 then cr_663_664 k h1 h else cr_664_666 k (by omega) h2
theorem cr_661_666 (k : ℕ) (h1 : 661 ≤ k) (h2 : k < 666) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 663 then cr_661_663 k h1 h else cr_663_666 k (by omega) h2
theorem cr_656_666 (k : ℕ) (h1 : 656 ≤ k) (h2 : k < 666) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 661 then cr_656_661 k h1 h else cr_661_666 k (by omega) h2
theorem cr_666_667 (k : ℕ) (h1 : 666 ≤ k) (h2 : k < 667) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 666 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf666_ok
theorem cr_667_668 (k : ℕ) (h1 : 667 ≤ k) (h2 : k < 668) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 667 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf667_ok
theorem cr_666_668 (k : ℕ) (h1 : 666 ≤ k) (h2 : k < 668) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 667 then cr_666_667 k h1 h else cr_667_668 k (by omega) h2
theorem cr_668_669 (k : ℕ) (h1 : 668 ≤ k) (h2 : k < 669) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 668 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf668_ok
theorem cr_669_670 (k : ℕ) (h1 : 669 ≤ k) (h2 : k < 670) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 669 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf669_ok
theorem cr_670_671 (k : ℕ) (h1 : 670 ≤ k) (h2 : k < 671) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 670 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf670_ok
theorem cr_669_671 (k : ℕ) (h1 : 669 ≤ k) (h2 : k < 671) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 670 then cr_669_670 k h1 h else cr_670_671 k (by omega) h2
theorem cr_668_671 (k : ℕ) (h1 : 668 ≤ k) (h2 : k < 671) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 669 then cr_668_669 k h1 h else cr_669_671 k (by omega) h2
theorem cr_666_671 (k : ℕ) (h1 : 666 ≤ k) (h2 : k < 671) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 668 then cr_666_668 k h1 h else cr_668_671 k (by omega) h2
theorem cr_671_672 (k : ℕ) (h1 : 671 ≤ k) (h2 : k < 672) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 671 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf671_ok
theorem cr_672_673 (k : ℕ) (h1 : 672 ≤ k) (h2 : k < 673) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 672 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf672_ok
theorem cr_671_673 (k : ℕ) (h1 : 671 ≤ k) (h2 : k < 673) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 672 then cr_671_672 k h1 h else cr_672_673 k (by omega) h2
theorem cr_673_674 (k : ℕ) (h1 : 673 ≤ k) (h2 : k < 674) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 673 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf673_ok
theorem cr_674_675 (k : ℕ) (h1 : 674 ≤ k) (h2 : k < 675) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 674 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf674_ok
theorem cr_675_676 (k : ℕ) (h1 : 675 ≤ k) (h2 : k < 676) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 675 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf675_ok
theorem cr_674_676 (k : ℕ) (h1 : 674 ≤ k) (h2 : k < 676) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 675 then cr_674_675 k h1 h else cr_675_676 k (by omega) h2
theorem cr_673_676 (k : ℕ) (h1 : 673 ≤ k) (h2 : k < 676) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 674 then cr_673_674 k h1 h else cr_674_676 k (by omega) h2
theorem cr_671_676 (k : ℕ) (h1 : 671 ≤ k) (h2 : k < 676) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 673 then cr_671_673 k h1 h else cr_673_676 k (by omega) h2
theorem cr_666_676 (k : ℕ) (h1 : 666 ≤ k) (h2 : k < 676) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 671 then cr_666_671 k h1 h else cr_671_676 k (by omega) h2
theorem cr_656_676 (k : ℕ) (h1 : 656 ≤ k) (h2 : k < 676) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 666 then cr_656_666 k h1 h else cr_666_676 k (by omega) h2
theorem cr_676_677 (k : ℕ) (h1 : 676 ≤ k) (h2 : k < 677) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 676 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf676_ok
theorem cr_677_678 (k : ℕ) (h1 : 677 ≤ k) (h2 : k < 678) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 677 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf677_ok
theorem cr_676_678 (k : ℕ) (h1 : 676 ≤ k) (h2 : k < 678) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 677 then cr_676_677 k h1 h else cr_677_678 k (by omega) h2
theorem cr_678_679 (k : ℕ) (h1 : 678 ≤ k) (h2 : k < 679) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 678 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf678_ok
theorem cr_679_680 (k : ℕ) (h1 : 679 ≤ k) (h2 : k < 680) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 679 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf679_ok
theorem cr_680_681 (k : ℕ) (h1 : 680 ≤ k) (h2 : k < 681) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 680 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf680_ok
theorem cr_679_681 (k : ℕ) (h1 : 679 ≤ k) (h2 : k < 681) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 680 then cr_679_680 k h1 h else cr_680_681 k (by omega) h2
theorem cr_678_681 (k : ℕ) (h1 : 678 ≤ k) (h2 : k < 681) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 679 then cr_678_679 k h1 h else cr_679_681 k (by omega) h2
theorem cr_676_681 (k : ℕ) (h1 : 676 ≤ k) (h2 : k < 681) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 678 then cr_676_678 k h1 h else cr_678_681 k (by omega) h2
theorem cr_681_682 (k : ℕ) (h1 : 681 ≤ k) (h2 : k < 682) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 681 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf681_ok
theorem cr_682_683 (k : ℕ) (h1 : 682 ≤ k) (h2 : k < 683) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 682 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf682_ok
theorem cr_681_683 (k : ℕ) (h1 : 681 ≤ k) (h2 : k < 683) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 682 then cr_681_682 k h1 h else cr_682_683 k (by omega) h2
theorem cr_683_684 (k : ℕ) (h1 : 683 ≤ k) (h2 : k < 684) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 683 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf683_ok
theorem cr_684_685 (k : ℕ) (h1 : 684 ≤ k) (h2 : k < 685) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 684 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf684_ok
theorem cr_685_686 (k : ℕ) (h1 : 685 ≤ k) (h2 : k < 686) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 685 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf685_ok
theorem cr_684_686 (k : ℕ) (h1 : 684 ≤ k) (h2 : k < 686) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 685 then cr_684_685 k h1 h else cr_685_686 k (by omega) h2
theorem cr_683_686 (k : ℕ) (h1 : 683 ≤ k) (h2 : k < 686) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 684 then cr_683_684 k h1 h else cr_684_686 k (by omega) h2
theorem cr_681_686 (k : ℕ) (h1 : 681 ≤ k) (h2 : k < 686) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 683 then cr_681_683 k h1 h else cr_683_686 k (by omega) h2
theorem cr_676_686 (k : ℕ) (h1 : 676 ≤ k) (h2 : k < 686) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 681 then cr_676_681 k h1 h else cr_681_686 k (by omega) h2
theorem cr_686_687 (k : ℕ) (h1 : 686 ≤ k) (h2 : k < 687) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 686 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf686_ok
theorem cr_687_688 (k : ℕ) (h1 : 687 ≤ k) (h2 : k < 688) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 687 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf687_ok
theorem cr_686_688 (k : ℕ) (h1 : 686 ≤ k) (h2 : k < 688) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 687 then cr_686_687 k h1 h else cr_687_688 k (by omega) h2
theorem cr_688_689 (k : ℕ) (h1 : 688 ≤ k) (h2 : k < 689) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 688 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf688_ok
theorem cr_689_690 (k : ℕ) (h1 : 689 ≤ k) (h2 : k < 690) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 689 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf689_ok
theorem cr_690_691 (k : ℕ) (h1 : 690 ≤ k) (h2 : k < 691) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 690 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf690_ok
theorem cr_689_691 (k : ℕ) (h1 : 689 ≤ k) (h2 : k < 691) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 690 then cr_689_690 k h1 h else cr_690_691 k (by omega) h2
theorem cr_688_691 (k : ℕ) (h1 : 688 ≤ k) (h2 : k < 691) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 689 then cr_688_689 k h1 h else cr_689_691 k (by omega) h2
theorem cr_686_691 (k : ℕ) (h1 : 686 ≤ k) (h2 : k < 691) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 688 then cr_686_688 k h1 h else cr_688_691 k (by omega) h2
theorem cr_691_692 (k : ℕ) (h1 : 691 ≤ k) (h2 : k < 692) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 691 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf691_ok
theorem cr_692_693 (k : ℕ) (h1 : 692 ≤ k) (h2 : k < 693) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 692 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf692_ok
theorem cr_693_694 (k : ℕ) (h1 : 693 ≤ k) (h2 : k < 694) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 693 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf693_ok
theorem cr_692_694 (k : ℕ) (h1 : 692 ≤ k) (h2 : k < 694) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 693 then cr_692_693 k h1 h else cr_693_694 k (by omega) h2
theorem cr_691_694 (k : ℕ) (h1 : 691 ≤ k) (h2 : k < 694) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 692 then cr_691_692 k h1 h else cr_692_694 k (by omega) h2
theorem cr_694_695 (k : ℕ) (h1 : 694 ≤ k) (h2 : k < 695) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 694 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf694_ok
theorem cr_695_696 (k : ℕ) (h1 : 695 ≤ k) (h2 : k < 696) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 695 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf695_ok
theorem cr_696_697 (k : ℕ) (h1 : 696 ≤ k) (h2 : k < 697) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 696 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf696_ok
theorem cr_695_697 (k : ℕ) (h1 : 695 ≤ k) (h2 : k < 697) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 696 then cr_695_696 k h1 h else cr_696_697 k (by omega) h2
theorem cr_694_697 (k : ℕ) (h1 : 694 ≤ k) (h2 : k < 697) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 695 then cr_694_695 k h1 h else cr_695_697 k (by omega) h2
theorem cr_691_697 (k : ℕ) (h1 : 691 ≤ k) (h2 : k < 697) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 694 then cr_691_694 k h1 h else cr_694_697 k (by omega) h2
theorem cr_686_697 (k : ℕ) (h1 : 686 ≤ k) (h2 : k < 697) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 691 then cr_686_691 k h1 h else cr_691_697 k (by omega) h2
theorem cr_676_697 (k : ℕ) (h1 : 676 ≤ k) (h2 : k < 697) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 686 then cr_676_686 k h1 h else cr_686_697 k (by omega) h2
theorem cr_656_697 (k : ℕ) (h1 : 656 ≤ k) (h2 : k < 697) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 676 then cr_656_676 k h1 h else cr_676_697 k (by omega) h2
theorem cr_697_698 (k : ℕ) (h1 : 697 ≤ k) (h2 : k < 698) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 697 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf697_ok
theorem cr_698_699 (k : ℕ) (h1 : 698 ≤ k) (h2 : k < 699) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 698 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf698_ok
theorem cr_697_699 (k : ℕ) (h1 : 697 ≤ k) (h2 : k < 699) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 698 then cr_697_698 k h1 h else cr_698_699 k (by omega) h2
theorem cr_699_700 (k : ℕ) (h1 : 699 ≤ k) (h2 : k < 700) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 699 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf699_ok
theorem cr_700_701 (k : ℕ) (h1 : 700 ≤ k) (h2 : k < 701) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 700 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf700_ok
theorem cr_701_702 (k : ℕ) (h1 : 701 ≤ k) (h2 : k < 702) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 701 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf701_ok
theorem cr_700_702 (k : ℕ) (h1 : 700 ≤ k) (h2 : k < 702) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 701 then cr_700_701 k h1 h else cr_701_702 k (by omega) h2
theorem cr_699_702 (k : ℕ) (h1 : 699 ≤ k) (h2 : k < 702) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 700 then cr_699_700 k h1 h else cr_700_702 k (by omega) h2
theorem cr_697_702 (k : ℕ) (h1 : 697 ≤ k) (h2 : k < 702) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 699 then cr_697_699 k h1 h else cr_699_702 k (by omega) h2
theorem cr_702_703 (k : ℕ) (h1 : 702 ≤ k) (h2 : k < 703) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 702 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf702_ok
theorem cr_703_704 (k : ℕ) (h1 : 703 ≤ k) (h2 : k < 704) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 703 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf703_ok
theorem cr_702_704 (k : ℕ) (h1 : 702 ≤ k) (h2 : k < 704) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 703 then cr_702_703 k h1 h else cr_703_704 k (by omega) h2
theorem cr_704_705 (k : ℕ) (h1 : 704 ≤ k) (h2 : k < 705) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 704 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf704_ok
theorem cr_705_706 (k : ℕ) (h1 : 705 ≤ k) (h2 : k < 706) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 705 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf705_ok
theorem cr_706_707 (k : ℕ) (h1 : 706 ≤ k) (h2 : k < 707) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 706 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf706_ok
theorem cr_705_707 (k : ℕ) (h1 : 705 ≤ k) (h2 : k < 707) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 706 then cr_705_706 k h1 h else cr_706_707 k (by omega) h2
theorem cr_704_707 (k : ℕ) (h1 : 704 ≤ k) (h2 : k < 707) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 705 then cr_704_705 k h1 h else cr_705_707 k (by omega) h2
theorem cr_702_707 (k : ℕ) (h1 : 702 ≤ k) (h2 : k < 707) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 704 then cr_702_704 k h1 h else cr_704_707 k (by omega) h2
theorem cr_697_707 (k : ℕ) (h1 : 697 ≤ k) (h2 : k < 707) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 702 then cr_697_702 k h1 h else cr_702_707 k (by omega) h2
theorem cr_707_708 (k : ℕ) (h1 : 707 ≤ k) (h2 : k < 708) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 707 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf707_ok
theorem cr_708_709 (k : ℕ) (h1 : 708 ≤ k) (h2 : k < 709) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 708 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf708_ok
theorem cr_707_709 (k : ℕ) (h1 : 707 ≤ k) (h2 : k < 709) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 708 then cr_707_708 k h1 h else cr_708_709 k (by omega) h2
theorem cr_709_710 (k : ℕ) (h1 : 709 ≤ k) (h2 : k < 710) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 709 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf709_ok
theorem cr_710_711 (k : ℕ) (h1 : 710 ≤ k) (h2 : k < 711) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 710 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf710_ok
theorem cr_711_712 (k : ℕ) (h1 : 711 ≤ k) (h2 : k < 712) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 711 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf711_ok
theorem cr_710_712 (k : ℕ) (h1 : 710 ≤ k) (h2 : k < 712) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 711 then cr_710_711 k h1 h else cr_711_712 k (by omega) h2
theorem cr_709_712 (k : ℕ) (h1 : 709 ≤ k) (h2 : k < 712) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 710 then cr_709_710 k h1 h else cr_710_712 k (by omega) h2
theorem cr_707_712 (k : ℕ) (h1 : 707 ≤ k) (h2 : k < 712) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 709 then cr_707_709 k h1 h else cr_709_712 k (by omega) h2
theorem cr_712_713 (k : ℕ) (h1 : 712 ≤ k) (h2 : k < 713) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 712 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf712_ok
theorem cr_713_714 (k : ℕ) (h1 : 713 ≤ k) (h2 : k < 714) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 713 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf713_ok
theorem cr_712_714 (k : ℕ) (h1 : 712 ≤ k) (h2 : k < 714) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 713 then cr_712_713 k h1 h else cr_713_714 k (by omega) h2
theorem cr_714_715 (k : ℕ) (h1 : 714 ≤ k) (h2 : k < 715) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 714 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf714_ok
theorem cr_715_716 (k : ℕ) (h1 : 715 ≤ k) (h2 : k < 716) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 715 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf715_ok
theorem cr_716_717 (k : ℕ) (h1 : 716 ≤ k) (h2 : k < 717) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 716 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf716_ok
theorem cr_715_717 (k : ℕ) (h1 : 715 ≤ k) (h2 : k < 717) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 716 then cr_715_716 k h1 h else cr_716_717 k (by omega) h2
theorem cr_714_717 (k : ℕ) (h1 : 714 ≤ k) (h2 : k < 717) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 715 then cr_714_715 k h1 h else cr_715_717 k (by omega) h2
theorem cr_712_717 (k : ℕ) (h1 : 712 ≤ k) (h2 : k < 717) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 714 then cr_712_714 k h1 h else cr_714_717 k (by omega) h2
theorem cr_707_717 (k : ℕ) (h1 : 707 ≤ k) (h2 : k < 717) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 712 then cr_707_712 k h1 h else cr_712_717 k (by omega) h2
theorem cr_697_717 (k : ℕ) (h1 : 697 ≤ k) (h2 : k < 717) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 707 then cr_697_707 k h1 h else cr_707_717 k (by omega) h2
theorem cr_717_718 (k : ℕ) (h1 : 717 ≤ k) (h2 : k < 718) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 717 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf717_ok
theorem cr_718_719 (k : ℕ) (h1 : 718 ≤ k) (h2 : k < 719) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 718 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf718_ok
theorem cr_717_719 (k : ℕ) (h1 : 717 ≤ k) (h2 : k < 719) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 718 then cr_717_718 k h1 h else cr_718_719 k (by omega) h2
theorem cr_719_720 (k : ℕ) (h1 : 719 ≤ k) (h2 : k < 720) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 719 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf719_ok
theorem cr_720_721 (k : ℕ) (h1 : 720 ≤ k) (h2 : k < 721) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 720 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf720_ok
theorem cr_721_722 (k : ℕ) (h1 : 721 ≤ k) (h2 : k < 722) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 721 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf721_ok
theorem cr_720_722 (k : ℕ) (h1 : 720 ≤ k) (h2 : k < 722) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 721 then cr_720_721 k h1 h else cr_721_722 k (by omega) h2
theorem cr_719_722 (k : ℕ) (h1 : 719 ≤ k) (h2 : k < 722) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 720 then cr_719_720 k h1 h else cr_720_722 k (by omega) h2
theorem cr_717_722 (k : ℕ) (h1 : 717 ≤ k) (h2 : k < 722) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 719 then cr_717_719 k h1 h else cr_719_722 k (by omega) h2
theorem cr_722_723 (k : ℕ) (h1 : 722 ≤ k) (h2 : k < 723) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 722 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf722_ok
theorem cr_723_724 (k : ℕ) (h1 : 723 ≤ k) (h2 : k < 724) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 723 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf723_ok
theorem cr_722_724 (k : ℕ) (h1 : 722 ≤ k) (h2 : k < 724) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 723 then cr_722_723 k h1 h else cr_723_724 k (by omega) h2
theorem cr_724_725 (k : ℕ) (h1 : 724 ≤ k) (h2 : k < 725) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 724 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf724_ok
theorem cr_725_726 (k : ℕ) (h1 : 725 ≤ k) (h2 : k < 726) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 725 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf725_ok
theorem cr_726_727 (k : ℕ) (h1 : 726 ≤ k) (h2 : k < 727) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 726 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf726_ok
theorem cr_725_727 (k : ℕ) (h1 : 725 ≤ k) (h2 : k < 727) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 726 then cr_725_726 k h1 h else cr_726_727 k (by omega) h2
theorem cr_724_727 (k : ℕ) (h1 : 724 ≤ k) (h2 : k < 727) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 725 then cr_724_725 k h1 h else cr_725_727 k (by omega) h2
theorem cr_722_727 (k : ℕ) (h1 : 722 ≤ k) (h2 : k < 727) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 724 then cr_722_724 k h1 h else cr_724_727 k (by omega) h2
theorem cr_717_727 (k : ℕ) (h1 : 717 ≤ k) (h2 : k < 727) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 722 then cr_717_722 k h1 h else cr_722_727 k (by omega) h2
theorem cr_727_728 (k : ℕ) (h1 : 727 ≤ k) (h2 : k < 728) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 727 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf727_ok
theorem cr_728_729 (k : ℕ) (h1 : 728 ≤ k) (h2 : k < 729) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 728 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf728_ok
theorem cr_727_729 (k : ℕ) (h1 : 727 ≤ k) (h2 : k < 729) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 728 then cr_727_728 k h1 h else cr_728_729 k (by omega) h2
theorem cr_729_730 (k : ℕ) (h1 : 729 ≤ k) (h2 : k < 730) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 729 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf729_ok
theorem cr_730_731 (k : ℕ) (h1 : 730 ≤ k) (h2 : k < 731) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 730 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf730_ok
theorem cr_731_732 (k : ℕ) (h1 : 731 ≤ k) (h2 : k < 732) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 731 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf731_ok
theorem cr_730_732 (k : ℕ) (h1 : 730 ≤ k) (h2 : k < 732) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 731 then cr_730_731 k h1 h else cr_731_732 k (by omega) h2
theorem cr_729_732 (k : ℕ) (h1 : 729 ≤ k) (h2 : k < 732) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 730 then cr_729_730 k h1 h else cr_730_732 k (by omega) h2
theorem cr_727_732 (k : ℕ) (h1 : 727 ≤ k) (h2 : k < 732) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 729 then cr_727_729 k h1 h else cr_729_732 k (by omega) h2
theorem cr_732_733 (k : ℕ) (h1 : 732 ≤ k) (h2 : k < 733) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 732 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf732_ok
theorem cr_733_734 (k : ℕ) (h1 : 733 ≤ k) (h2 : k < 734) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 733 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf733_ok
theorem cr_734_735 (k : ℕ) (h1 : 734 ≤ k) (h2 : k < 735) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 734 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf734_ok
theorem cr_733_735 (k : ℕ) (h1 : 733 ≤ k) (h2 : k < 735) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 734 then cr_733_734 k h1 h else cr_734_735 k (by omega) h2
theorem cr_732_735 (k : ℕ) (h1 : 732 ≤ k) (h2 : k < 735) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 733 then cr_732_733 k h1 h else cr_733_735 k (by omega) h2
theorem cr_735_736 (k : ℕ) (h1 : 735 ≤ k) (h2 : k < 736) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 735 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf735_ok
theorem cr_736_737 (k : ℕ) (h1 : 736 ≤ k) (h2 : k < 737) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 736 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf736_ok
theorem cr_737_738 (k : ℕ) (h1 : 737 ≤ k) (h2 : k < 738) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 737 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf737_ok
theorem cr_736_738 (k : ℕ) (h1 : 736 ≤ k) (h2 : k < 738) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 737 then cr_736_737 k h1 h else cr_737_738 k (by omega) h2
theorem cr_735_738 (k : ℕ) (h1 : 735 ≤ k) (h2 : k < 738) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 736 then cr_735_736 k h1 h else cr_736_738 k (by omega) h2
theorem cr_732_738 (k : ℕ) (h1 : 732 ≤ k) (h2 : k < 738) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 735 then cr_732_735 k h1 h else cr_735_738 k (by omega) h2
theorem cr_727_738 (k : ℕ) (h1 : 727 ≤ k) (h2 : k < 738) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 732 then cr_727_732 k h1 h else cr_732_738 k (by omega) h2
theorem cr_717_738 (k : ℕ) (h1 : 717 ≤ k) (h2 : k < 738) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 727 then cr_717_727 k h1 h else cr_727_738 k (by omega) h2
theorem cr_697_738 (k : ℕ) (h1 : 697 ≤ k) (h2 : k < 738) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 717 then cr_697_717 k h1 h else cr_717_738 k (by omega) h2
theorem cr_656_738 (k : ℕ) (h1 : 656 ≤ k) (h2 : k < 738) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 697 then cr_656_697 k h1 h else cr_697_738 k (by omega) h2
theorem cr_738_739 (k : ℕ) (h1 : 738 ≤ k) (h2 : k < 739) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 738 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf738_ok
theorem cr_739_740 (k : ℕ) (h1 : 739 ≤ k) (h2 : k < 740) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 739 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf739_ok
theorem cr_738_740 (k : ℕ) (h1 : 738 ≤ k) (h2 : k < 740) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 739 then cr_738_739 k h1 h else cr_739_740 k (by omega) h2
theorem cr_740_741 (k : ℕ) (h1 : 740 ≤ k) (h2 : k < 741) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 740 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf740_ok
theorem cr_741_742 (k : ℕ) (h1 : 741 ≤ k) (h2 : k < 742) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 741 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf741_ok
theorem cr_742_743 (k : ℕ) (h1 : 742 ≤ k) (h2 : k < 743) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 742 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf742_ok
theorem cr_741_743 (k : ℕ) (h1 : 741 ≤ k) (h2 : k < 743) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 742 then cr_741_742 k h1 h else cr_742_743 k (by omega) h2
theorem cr_740_743 (k : ℕ) (h1 : 740 ≤ k) (h2 : k < 743) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 741 then cr_740_741 k h1 h else cr_741_743 k (by omega) h2
theorem cr_738_743 (k : ℕ) (h1 : 738 ≤ k) (h2 : k < 743) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 740 then cr_738_740 k h1 h else cr_740_743 k (by omega) h2
theorem cr_743_744 (k : ℕ) (h1 : 743 ≤ k) (h2 : k < 744) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 743 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf743_ok
theorem cr_744_745 (k : ℕ) (h1 : 744 ≤ k) (h2 : k < 745) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 744 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf744_ok
theorem cr_743_745 (k : ℕ) (h1 : 743 ≤ k) (h2 : k < 745) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 744 then cr_743_744 k h1 h else cr_744_745 k (by omega) h2
theorem cr_745_746 (k : ℕ) (h1 : 745 ≤ k) (h2 : k < 746) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 745 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf745_ok
theorem cr_746_747 (k : ℕ) (h1 : 746 ≤ k) (h2 : k < 747) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 746 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf746_ok
theorem cr_747_748 (k : ℕ) (h1 : 747 ≤ k) (h2 : k < 748) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 747 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf747_ok
theorem cr_746_748 (k : ℕ) (h1 : 746 ≤ k) (h2 : k < 748) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 747 then cr_746_747 k h1 h else cr_747_748 k (by omega) h2
theorem cr_745_748 (k : ℕ) (h1 : 745 ≤ k) (h2 : k < 748) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 746 then cr_745_746 k h1 h else cr_746_748 k (by omega) h2
theorem cr_743_748 (k : ℕ) (h1 : 743 ≤ k) (h2 : k < 748) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 745 then cr_743_745 k h1 h else cr_745_748 k (by omega) h2
theorem cr_738_748 (k : ℕ) (h1 : 738 ≤ k) (h2 : k < 748) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 743 then cr_738_743 k h1 h else cr_743_748 k (by omega) h2
theorem cr_748_749 (k : ℕ) (h1 : 748 ≤ k) (h2 : k < 749) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 748 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf748_ok
theorem cr_749_750 (k : ℕ) (h1 : 749 ≤ k) (h2 : k < 750) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 749 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf749_ok
theorem cr_748_750 (k : ℕ) (h1 : 748 ≤ k) (h2 : k < 750) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 749 then cr_748_749 k h1 h else cr_749_750 k (by omega) h2
theorem cr_750_751 (k : ℕ) (h1 : 750 ≤ k) (h2 : k < 751) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 750 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf750_ok
theorem cr_751_752 (k : ℕ) (h1 : 751 ≤ k) (h2 : k < 752) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 751 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf751_ok
theorem cr_752_753 (k : ℕ) (h1 : 752 ≤ k) (h2 : k < 753) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 752 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf752_ok
theorem cr_751_753 (k : ℕ) (h1 : 751 ≤ k) (h2 : k < 753) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 752 then cr_751_752 k h1 h else cr_752_753 k (by omega) h2
theorem cr_750_753 (k : ℕ) (h1 : 750 ≤ k) (h2 : k < 753) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 751 then cr_750_751 k h1 h else cr_751_753 k (by omega) h2
theorem cr_748_753 (k : ℕ) (h1 : 748 ≤ k) (h2 : k < 753) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 750 then cr_748_750 k h1 h else cr_750_753 k (by omega) h2
theorem cr_753_754 (k : ℕ) (h1 : 753 ≤ k) (h2 : k < 754) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 753 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf753_ok
theorem cr_754_755 (k : ℕ) (h1 : 754 ≤ k) (h2 : k < 755) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 754 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf754_ok
theorem cr_753_755 (k : ℕ) (h1 : 753 ≤ k) (h2 : k < 755) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 754 then cr_753_754 k h1 h else cr_754_755 k (by omega) h2
theorem cr_755_756 (k : ℕ) (h1 : 755 ≤ k) (h2 : k < 756) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 755 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf755_ok
theorem cr_756_757 (k : ℕ) (h1 : 756 ≤ k) (h2 : k < 757) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 756 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf756_ok
theorem cr_757_758 (k : ℕ) (h1 : 757 ≤ k) (h2 : k < 758) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 757 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf757_ok
theorem cr_756_758 (k : ℕ) (h1 : 756 ≤ k) (h2 : k < 758) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 757 then cr_756_757 k h1 h else cr_757_758 k (by omega) h2
theorem cr_755_758 (k : ℕ) (h1 : 755 ≤ k) (h2 : k < 758) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 756 then cr_755_756 k h1 h else cr_756_758 k (by omega) h2
theorem cr_753_758 (k : ℕ) (h1 : 753 ≤ k) (h2 : k < 758) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 755 then cr_753_755 k h1 h else cr_755_758 k (by omega) h2
theorem cr_748_758 (k : ℕ) (h1 : 748 ≤ k) (h2 : k < 758) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 753 then cr_748_753 k h1 h else cr_753_758 k (by omega) h2
theorem cr_738_758 (k : ℕ) (h1 : 738 ≤ k) (h2 : k < 758) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 748 then cr_738_748 k h1 h else cr_748_758 k (by omega) h2
theorem cr_758_759 (k : ℕ) (h1 : 758 ≤ k) (h2 : k < 759) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 758 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf758_ok
theorem cr_759_760 (k : ℕ) (h1 : 759 ≤ k) (h2 : k < 760) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 759 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf759_ok
theorem cr_758_760 (k : ℕ) (h1 : 758 ≤ k) (h2 : k < 760) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 759 then cr_758_759 k h1 h else cr_759_760 k (by omega) h2
theorem cr_760_761 (k : ℕ) (h1 : 760 ≤ k) (h2 : k < 761) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 760 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf760_ok
theorem cr_761_762 (k : ℕ) (h1 : 761 ≤ k) (h2 : k < 762) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 761 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf761_ok
theorem cr_762_763 (k : ℕ) (h1 : 762 ≤ k) (h2 : k < 763) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 762 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf762_ok
theorem cr_761_763 (k : ℕ) (h1 : 761 ≤ k) (h2 : k < 763) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 762 then cr_761_762 k h1 h else cr_762_763 k (by omega) h2
theorem cr_760_763 (k : ℕ) (h1 : 760 ≤ k) (h2 : k < 763) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 761 then cr_760_761 k h1 h else cr_761_763 k (by omega) h2
theorem cr_758_763 (k : ℕ) (h1 : 758 ≤ k) (h2 : k < 763) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 760 then cr_758_760 k h1 h else cr_760_763 k (by omega) h2
theorem cr_763_764 (k : ℕ) (h1 : 763 ≤ k) (h2 : k < 764) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 763 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf763_ok
theorem cr_764_765 (k : ℕ) (h1 : 764 ≤ k) (h2 : k < 765) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 764 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf764_ok
theorem cr_763_765 (k : ℕ) (h1 : 763 ≤ k) (h2 : k < 765) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 764 then cr_763_764 k h1 h else cr_764_765 k (by omega) h2
theorem cr_765_766 (k : ℕ) (h1 : 765 ≤ k) (h2 : k < 766) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 765 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf765_ok
theorem cr_766_767 (k : ℕ) (h1 : 766 ≤ k) (h2 : k < 767) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 766 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf766_ok
theorem cr_767_768 (k : ℕ) (h1 : 767 ≤ k) (h2 : k < 768) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 767 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf767_ok
theorem cr_766_768 (k : ℕ) (h1 : 766 ≤ k) (h2 : k < 768) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 767 then cr_766_767 k h1 h else cr_767_768 k (by omega) h2
theorem cr_765_768 (k : ℕ) (h1 : 765 ≤ k) (h2 : k < 768) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 766 then cr_765_766 k h1 h else cr_766_768 k (by omega) h2
theorem cr_763_768 (k : ℕ) (h1 : 763 ≤ k) (h2 : k < 768) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 765 then cr_763_765 k h1 h else cr_765_768 k (by omega) h2
theorem cr_758_768 (k : ℕ) (h1 : 758 ≤ k) (h2 : k < 768) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 763 then cr_758_763 k h1 h else cr_763_768 k (by omega) h2
theorem cr_768_769 (k : ℕ) (h1 : 768 ≤ k) (h2 : k < 769) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 768 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf768_ok
theorem cr_769_770 (k : ℕ) (h1 : 769 ≤ k) (h2 : k < 770) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 769 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf769_ok
theorem cr_768_770 (k : ℕ) (h1 : 768 ≤ k) (h2 : k < 770) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 769 then cr_768_769 k h1 h else cr_769_770 k (by omega) h2
theorem cr_770_771 (k : ℕ) (h1 : 770 ≤ k) (h2 : k < 771) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 770 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf770_ok
theorem cr_771_772 (k : ℕ) (h1 : 771 ≤ k) (h2 : k < 772) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 771 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf771_ok
theorem cr_772_773 (k : ℕ) (h1 : 772 ≤ k) (h2 : k < 773) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 772 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf772_ok
theorem cr_771_773 (k : ℕ) (h1 : 771 ≤ k) (h2 : k < 773) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 772 then cr_771_772 k h1 h else cr_772_773 k (by omega) h2
theorem cr_770_773 (k : ℕ) (h1 : 770 ≤ k) (h2 : k < 773) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 771 then cr_770_771 k h1 h else cr_771_773 k (by omega) h2
theorem cr_768_773 (k : ℕ) (h1 : 768 ≤ k) (h2 : k < 773) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 770 then cr_768_770 k h1 h else cr_770_773 k (by omega) h2
theorem cr_773_774 (k : ℕ) (h1 : 773 ≤ k) (h2 : k < 774) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 773 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf773_ok
theorem cr_774_775 (k : ℕ) (h1 : 774 ≤ k) (h2 : k < 775) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 774 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf774_ok
theorem cr_775_776 (k : ℕ) (h1 : 775 ≤ k) (h2 : k < 776) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 775 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf775_ok
theorem cr_774_776 (k : ℕ) (h1 : 774 ≤ k) (h2 : k < 776) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 775 then cr_774_775 k h1 h else cr_775_776 k (by omega) h2
theorem cr_773_776 (k : ℕ) (h1 : 773 ≤ k) (h2 : k < 776) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 774 then cr_773_774 k h1 h else cr_774_776 k (by omega) h2
theorem cr_776_777 (k : ℕ) (h1 : 776 ≤ k) (h2 : k < 777) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 776 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf776_ok
theorem cr_777_778 (k : ℕ) (h1 : 777 ≤ k) (h2 : k < 778) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 777 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf777_ok
theorem cr_778_779 (k : ℕ) (h1 : 778 ≤ k) (h2 : k < 779) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 778 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf778_ok
theorem cr_777_779 (k : ℕ) (h1 : 777 ≤ k) (h2 : k < 779) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 778 then cr_777_778 k h1 h else cr_778_779 k (by omega) h2
theorem cr_776_779 (k : ℕ) (h1 : 776 ≤ k) (h2 : k < 779) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 777 then cr_776_777 k h1 h else cr_777_779 k (by omega) h2
theorem cr_773_779 (k : ℕ) (h1 : 773 ≤ k) (h2 : k < 779) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 776 then cr_773_776 k h1 h else cr_776_779 k (by omega) h2
theorem cr_768_779 (k : ℕ) (h1 : 768 ≤ k) (h2 : k < 779) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 773 then cr_768_773 k h1 h else cr_773_779 k (by omega) h2
theorem cr_758_779 (k : ℕ) (h1 : 758 ≤ k) (h2 : k < 779) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 768 then cr_758_768 k h1 h else cr_768_779 k (by omega) h2
theorem cr_738_779 (k : ℕ) (h1 : 738 ≤ k) (h2 : k < 779) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 758 then cr_738_758 k h1 h else cr_758_779 k (by omega) h2
theorem cr_779_780 (k : ℕ) (h1 : 779 ≤ k) (h2 : k < 780) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 779 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf779_ok
theorem cr_780_781 (k : ℕ) (h1 : 780 ≤ k) (h2 : k < 781) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 780 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf780_ok
theorem cr_779_781 (k : ℕ) (h1 : 779 ≤ k) (h2 : k < 781) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 780 then cr_779_780 k h1 h else cr_780_781 k (by omega) h2
theorem cr_781_782 (k : ℕ) (h1 : 781 ≤ k) (h2 : k < 782) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 781 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf781_ok
theorem cr_782_783 (k : ℕ) (h1 : 782 ≤ k) (h2 : k < 783) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 782 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf782_ok
theorem cr_783_784 (k : ℕ) (h1 : 783 ≤ k) (h2 : k < 784) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 783 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf783_ok
theorem cr_782_784 (k : ℕ) (h1 : 782 ≤ k) (h2 : k < 784) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 783 then cr_782_783 k h1 h else cr_783_784 k (by omega) h2
theorem cr_781_784 (k : ℕ) (h1 : 781 ≤ k) (h2 : k < 784) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 782 then cr_781_782 k h1 h else cr_782_784 k (by omega) h2
theorem cr_779_784 (k : ℕ) (h1 : 779 ≤ k) (h2 : k < 784) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 781 then cr_779_781 k h1 h else cr_781_784 k (by omega) h2
theorem cr_784_785 (k : ℕ) (h1 : 784 ≤ k) (h2 : k < 785) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 784 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf784_ok
theorem cr_785_786 (k : ℕ) (h1 : 785 ≤ k) (h2 : k < 786) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 785 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf785_ok
theorem cr_784_786 (k : ℕ) (h1 : 784 ≤ k) (h2 : k < 786) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 785 then cr_784_785 k h1 h else cr_785_786 k (by omega) h2
theorem cr_786_787 (k : ℕ) (h1 : 786 ≤ k) (h2 : k < 787) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 786 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf786_ok
theorem cr_787_788 (k : ℕ) (h1 : 787 ≤ k) (h2 : k < 788) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 787 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf787_ok
theorem cr_788_789 (k : ℕ) (h1 : 788 ≤ k) (h2 : k < 789) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 788 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf788_ok
theorem cr_787_789 (k : ℕ) (h1 : 787 ≤ k) (h2 : k < 789) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 788 then cr_787_788 k h1 h else cr_788_789 k (by omega) h2
theorem cr_786_789 (k : ℕ) (h1 : 786 ≤ k) (h2 : k < 789) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 787 then cr_786_787 k h1 h else cr_787_789 k (by omega) h2
theorem cr_784_789 (k : ℕ) (h1 : 784 ≤ k) (h2 : k < 789) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 786 then cr_784_786 k h1 h else cr_786_789 k (by omega) h2
theorem cr_779_789 (k : ℕ) (h1 : 779 ≤ k) (h2 : k < 789) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 784 then cr_779_784 k h1 h else cr_784_789 k (by omega) h2
theorem cr_789_790 (k : ℕ) (h1 : 789 ≤ k) (h2 : k < 790) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 789 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf789_ok
theorem cr_790_791 (k : ℕ) (h1 : 790 ≤ k) (h2 : k < 791) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 790 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf790_ok
theorem cr_789_791 (k : ℕ) (h1 : 789 ≤ k) (h2 : k < 791) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 790 then cr_789_790 k h1 h else cr_790_791 k (by omega) h2
theorem cr_791_792 (k : ℕ) (h1 : 791 ≤ k) (h2 : k < 792) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 791 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf791_ok
theorem cr_792_793 (k : ℕ) (h1 : 792 ≤ k) (h2 : k < 793) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 792 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf792_ok
theorem cr_793_794 (k : ℕ) (h1 : 793 ≤ k) (h2 : k < 794) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 793 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf793_ok
theorem cr_792_794 (k : ℕ) (h1 : 792 ≤ k) (h2 : k < 794) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 793 then cr_792_793 k h1 h else cr_793_794 k (by omega) h2
theorem cr_791_794 (k : ℕ) (h1 : 791 ≤ k) (h2 : k < 794) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 792 then cr_791_792 k h1 h else cr_792_794 k (by omega) h2
theorem cr_789_794 (k : ℕ) (h1 : 789 ≤ k) (h2 : k < 794) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 791 then cr_789_791 k h1 h else cr_791_794 k (by omega) h2
theorem cr_794_795 (k : ℕ) (h1 : 794 ≤ k) (h2 : k < 795) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 794 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf794_ok
theorem cr_795_796 (k : ℕ) (h1 : 795 ≤ k) (h2 : k < 796) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 795 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf795_ok
theorem cr_794_796 (k : ℕ) (h1 : 794 ≤ k) (h2 : k < 796) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 795 then cr_794_795 k h1 h else cr_795_796 k (by omega) h2
theorem cr_796_797 (k : ℕ) (h1 : 796 ≤ k) (h2 : k < 797) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 796 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf796_ok
theorem cr_797_798 (k : ℕ) (h1 : 797 ≤ k) (h2 : k < 798) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 797 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf797_ok
theorem cr_798_799 (k : ℕ) (h1 : 798 ≤ k) (h2 : k < 799) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 798 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf798_ok
theorem cr_797_799 (k : ℕ) (h1 : 797 ≤ k) (h2 : k < 799) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 798 then cr_797_798 k h1 h else cr_798_799 k (by omega) h2
theorem cr_796_799 (k : ℕ) (h1 : 796 ≤ k) (h2 : k < 799) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 797 then cr_796_797 k h1 h else cr_797_799 k (by omega) h2
theorem cr_794_799 (k : ℕ) (h1 : 794 ≤ k) (h2 : k < 799) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 796 then cr_794_796 k h1 h else cr_796_799 k (by omega) h2
theorem cr_789_799 (k : ℕ) (h1 : 789 ≤ k) (h2 : k < 799) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 794 then cr_789_794 k h1 h else cr_794_799 k (by omega) h2
theorem cr_779_799 (k : ℕ) (h1 : 779 ≤ k) (h2 : k < 799) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 789 then cr_779_789 k h1 h else cr_789_799 k (by omega) h2
theorem cr_799_800 (k : ℕ) (h1 : 799 ≤ k) (h2 : k < 800) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 799 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf799_ok
theorem cr_800_801 (k : ℕ) (h1 : 800 ≤ k) (h2 : k < 801) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 800 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf800_ok
theorem cr_799_801 (k : ℕ) (h1 : 799 ≤ k) (h2 : k < 801) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 800 then cr_799_800 k h1 h else cr_800_801 k (by omega) h2
theorem cr_801_802 (k : ℕ) (h1 : 801 ≤ k) (h2 : k < 802) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 801 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf801_ok
theorem cr_802_803 (k : ℕ) (h1 : 802 ≤ k) (h2 : k < 803) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 802 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf802_ok
theorem cr_803_804 (k : ℕ) (h1 : 803 ≤ k) (h2 : k < 804) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 803 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf803_ok
theorem cr_802_804 (k : ℕ) (h1 : 802 ≤ k) (h2 : k < 804) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 803 then cr_802_803 k h1 h else cr_803_804 k (by omega) h2
theorem cr_801_804 (k : ℕ) (h1 : 801 ≤ k) (h2 : k < 804) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 802 then cr_801_802 k h1 h else cr_802_804 k (by omega) h2
theorem cr_799_804 (k : ℕ) (h1 : 799 ≤ k) (h2 : k < 804) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 801 then cr_799_801 k h1 h else cr_801_804 k (by omega) h2
theorem cr_804_805 (k : ℕ) (h1 : 804 ≤ k) (h2 : k < 805) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 804 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf804_ok
theorem cr_805_806 (k : ℕ) (h1 : 805 ≤ k) (h2 : k < 806) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 805 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf805_ok
theorem cr_804_806 (k : ℕ) (h1 : 804 ≤ k) (h2 : k < 806) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 805 then cr_804_805 k h1 h else cr_805_806 k (by omega) h2
theorem cr_806_807 (k : ℕ) (h1 : 806 ≤ k) (h2 : k < 807) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 806 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf806_ok
theorem cr_807_808 (k : ℕ) (h1 : 807 ≤ k) (h2 : k < 808) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 807 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf807_ok
theorem cr_808_809 (k : ℕ) (h1 : 808 ≤ k) (h2 : k < 809) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 808 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf808_ok
theorem cr_807_809 (k : ℕ) (h1 : 807 ≤ k) (h2 : k < 809) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 808 then cr_807_808 k h1 h else cr_808_809 k (by omega) h2
theorem cr_806_809 (k : ℕ) (h1 : 806 ≤ k) (h2 : k < 809) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 807 then cr_806_807 k h1 h else cr_807_809 k (by omega) h2
theorem cr_804_809 (k : ℕ) (h1 : 804 ≤ k) (h2 : k < 809) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 806 then cr_804_806 k h1 h else cr_806_809 k (by omega) h2
theorem cr_799_809 (k : ℕ) (h1 : 799 ≤ k) (h2 : k < 809) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 804 then cr_799_804 k h1 h else cr_804_809 k (by omega) h2
theorem cr_809_810 (k : ℕ) (h1 : 809 ≤ k) (h2 : k < 810) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 809 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf809_ok
theorem cr_810_811 (k : ℕ) (h1 : 810 ≤ k) (h2 : k < 811) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 810 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf810_ok
theorem cr_809_811 (k : ℕ) (h1 : 809 ≤ k) (h2 : k < 811) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 810 then cr_809_810 k h1 h else cr_810_811 k (by omega) h2
theorem cr_811_812 (k : ℕ) (h1 : 811 ≤ k) (h2 : k < 812) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 811 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf811_ok
theorem cr_812_813 (k : ℕ) (h1 : 812 ≤ k) (h2 : k < 813) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 812 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf812_ok
theorem cr_813_814 (k : ℕ) (h1 : 813 ≤ k) (h2 : k < 814) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 813 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf813_ok
theorem cr_812_814 (k : ℕ) (h1 : 812 ≤ k) (h2 : k < 814) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 813 then cr_812_813 k h1 h else cr_813_814 k (by omega) h2
theorem cr_811_814 (k : ℕ) (h1 : 811 ≤ k) (h2 : k < 814) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 812 then cr_811_812 k h1 h else cr_812_814 k (by omega) h2
theorem cr_809_814 (k : ℕ) (h1 : 809 ≤ k) (h2 : k < 814) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 811 then cr_809_811 k h1 h else cr_811_814 k (by omega) h2
theorem cr_814_815 (k : ℕ) (h1 : 814 ≤ k) (h2 : k < 815) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 814 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf814_ok
theorem cr_815_816 (k : ℕ) (h1 : 815 ≤ k) (h2 : k < 816) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 815 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf815_ok
theorem cr_816_817 (k : ℕ) (h1 : 816 ≤ k) (h2 : k < 817) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 816 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf816_ok
theorem cr_815_817 (k : ℕ) (h1 : 815 ≤ k) (h2 : k < 817) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 816 then cr_815_816 k h1 h else cr_816_817 k (by omega) h2
theorem cr_814_817 (k : ℕ) (h1 : 814 ≤ k) (h2 : k < 817) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 815 then cr_814_815 k h1 h else cr_815_817 k (by omega) h2
theorem cr_817_818 (k : ℕ) (h1 : 817 ≤ k) (h2 : k < 818) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 817 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf817_ok
theorem cr_818_819 (k : ℕ) (h1 : 818 ≤ k) (h2 : k < 819) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 818 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf818_ok
theorem cr_819_820 (k : ℕ) (h1 : 819 ≤ k) (h2 : k < 820) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 819 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf819_ok
theorem cr_818_820 (k : ℕ) (h1 : 818 ≤ k) (h2 : k < 820) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 819 then cr_818_819 k h1 h else cr_819_820 k (by omega) h2
theorem cr_817_820 (k : ℕ) (h1 : 817 ≤ k) (h2 : k < 820) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 818 then cr_817_818 k h1 h else cr_818_820 k (by omega) h2
theorem cr_814_820 (k : ℕ) (h1 : 814 ≤ k) (h2 : k < 820) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 817 then cr_814_817 k h1 h else cr_817_820 k (by omega) h2
theorem cr_809_820 (k : ℕ) (h1 : 809 ≤ k) (h2 : k < 820) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 814 then cr_809_814 k h1 h else cr_814_820 k (by omega) h2
theorem cr_799_820 (k : ℕ) (h1 : 799 ≤ k) (h2 : k < 820) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 809 then cr_799_809 k h1 h else cr_809_820 k (by omega) h2
theorem cr_779_820 (k : ℕ) (h1 : 779 ≤ k) (h2 : k < 820) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 799 then cr_779_799 k h1 h else cr_799_820 k (by omega) h2
theorem cr_738_820 (k : ℕ) (h1 : 738 ≤ k) (h2 : k < 820) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 779 then cr_738_779 k h1 h else cr_779_820 k (by omega) h2
theorem cr_656_820 (k : ℕ) (h1 : 656 ≤ k) (h2 : k < 820) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 738 then cr_656_738 k h1 h else cr_738_820 k (by omega) h2
theorem cr_820_821 (k : ℕ) (h1 : 820 ≤ k) (h2 : k < 821) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 820 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf820_ok
theorem cr_821_822 (k : ℕ) (h1 : 821 ≤ k) (h2 : k < 822) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 821 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf821_ok
theorem cr_820_822 (k : ℕ) (h1 : 820 ≤ k) (h2 : k < 822) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 821 then cr_820_821 k h1 h else cr_821_822 k (by omega) h2
theorem cr_822_823 (k : ℕ) (h1 : 822 ≤ k) (h2 : k < 823) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 822 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf822_ok
theorem cr_823_824 (k : ℕ) (h1 : 823 ≤ k) (h2 : k < 824) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 823 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf823_ok
theorem cr_824_825 (k : ℕ) (h1 : 824 ≤ k) (h2 : k < 825) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 824 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf824_ok
theorem cr_823_825 (k : ℕ) (h1 : 823 ≤ k) (h2 : k < 825) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 824 then cr_823_824 k h1 h else cr_824_825 k (by omega) h2
theorem cr_822_825 (k : ℕ) (h1 : 822 ≤ k) (h2 : k < 825) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 823 then cr_822_823 k h1 h else cr_823_825 k (by omega) h2
theorem cr_820_825 (k : ℕ) (h1 : 820 ≤ k) (h2 : k < 825) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 822 then cr_820_822 k h1 h else cr_822_825 k (by omega) h2
theorem cr_825_826 (k : ℕ) (h1 : 825 ≤ k) (h2 : k < 826) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 825 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf825_ok
theorem cr_826_827 (k : ℕ) (h1 : 826 ≤ k) (h2 : k < 827) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 826 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf826_ok
theorem cr_825_827 (k : ℕ) (h1 : 825 ≤ k) (h2 : k < 827) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 826 then cr_825_826 k h1 h else cr_826_827 k (by omega) h2
theorem cr_827_828 (k : ℕ) (h1 : 827 ≤ k) (h2 : k < 828) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 827 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf827_ok
theorem cr_828_829 (k : ℕ) (h1 : 828 ≤ k) (h2 : k < 829) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 828 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf828_ok
theorem cr_829_830 (k : ℕ) (h1 : 829 ≤ k) (h2 : k < 830) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 829 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf829_ok
theorem cr_828_830 (k : ℕ) (h1 : 828 ≤ k) (h2 : k < 830) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 829 then cr_828_829 k h1 h else cr_829_830 k (by omega) h2
theorem cr_827_830 (k : ℕ) (h1 : 827 ≤ k) (h2 : k < 830) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 828 then cr_827_828 k h1 h else cr_828_830 k (by omega) h2
theorem cr_825_830 (k : ℕ) (h1 : 825 ≤ k) (h2 : k < 830) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 827 then cr_825_827 k h1 h else cr_827_830 k (by omega) h2
theorem cr_820_830 (k : ℕ) (h1 : 820 ≤ k) (h2 : k < 830) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 825 then cr_820_825 k h1 h else cr_825_830 k (by omega) h2
theorem cr_830_831 (k : ℕ) (h1 : 830 ≤ k) (h2 : k < 831) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 830 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf830_ok
theorem cr_831_832 (k : ℕ) (h1 : 831 ≤ k) (h2 : k < 832) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 831 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf831_ok
theorem cr_830_832 (k : ℕ) (h1 : 830 ≤ k) (h2 : k < 832) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 831 then cr_830_831 k h1 h else cr_831_832 k (by omega) h2
theorem cr_832_833 (k : ℕ) (h1 : 832 ≤ k) (h2 : k < 833) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 832 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf832_ok
theorem cr_833_834 (k : ℕ) (h1 : 833 ≤ k) (h2 : k < 834) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 833 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf833_ok
theorem cr_834_835 (k : ℕ) (h1 : 834 ≤ k) (h2 : k < 835) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 834 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf834_ok
theorem cr_833_835 (k : ℕ) (h1 : 833 ≤ k) (h2 : k < 835) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 834 then cr_833_834 k h1 h else cr_834_835 k (by omega) h2
theorem cr_832_835 (k : ℕ) (h1 : 832 ≤ k) (h2 : k < 835) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 833 then cr_832_833 k h1 h else cr_833_835 k (by omega) h2
theorem cr_830_835 (k : ℕ) (h1 : 830 ≤ k) (h2 : k < 835) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 832 then cr_830_832 k h1 h else cr_832_835 k (by omega) h2
theorem cr_835_836 (k : ℕ) (h1 : 835 ≤ k) (h2 : k < 836) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 835 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf835_ok
theorem cr_836_837 (k : ℕ) (h1 : 836 ≤ k) (h2 : k < 837) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 836 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf836_ok
theorem cr_835_837 (k : ℕ) (h1 : 835 ≤ k) (h2 : k < 837) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 836 then cr_835_836 k h1 h else cr_836_837 k (by omega) h2
theorem cr_837_838 (k : ℕ) (h1 : 837 ≤ k) (h2 : k < 838) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 837 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf837_ok
theorem cr_838_839 (k : ℕ) (h1 : 838 ≤ k) (h2 : k < 839) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 838 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf838_ok
theorem cr_839_840 (k : ℕ) (h1 : 839 ≤ k) (h2 : k < 840) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 839 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf839_ok
theorem cr_838_840 (k : ℕ) (h1 : 838 ≤ k) (h2 : k < 840) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 839 then cr_838_839 k h1 h else cr_839_840 k (by omega) h2
theorem cr_837_840 (k : ℕ) (h1 : 837 ≤ k) (h2 : k < 840) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 838 then cr_837_838 k h1 h else cr_838_840 k (by omega) h2
theorem cr_835_840 (k : ℕ) (h1 : 835 ≤ k) (h2 : k < 840) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 837 then cr_835_837 k h1 h else cr_837_840 k (by omega) h2
theorem cr_830_840 (k : ℕ) (h1 : 830 ≤ k) (h2 : k < 840) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 835 then cr_830_835 k h1 h else cr_835_840 k (by omega) h2
theorem cr_820_840 (k : ℕ) (h1 : 820 ≤ k) (h2 : k < 840) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 830 then cr_820_830 k h1 h else cr_830_840 k (by omega) h2
theorem cr_840_841 (k : ℕ) (h1 : 840 ≤ k) (h2 : k < 841) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 840 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf840_ok
theorem cr_841_842 (k : ℕ) (h1 : 841 ≤ k) (h2 : k < 842) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 841 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf841_ok
theorem cr_840_842 (k : ℕ) (h1 : 840 ≤ k) (h2 : k < 842) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 841 then cr_840_841 k h1 h else cr_841_842 k (by omega) h2
theorem cr_842_843 (k : ℕ) (h1 : 842 ≤ k) (h2 : k < 843) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 842 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf842_ok
theorem cr_843_844 (k : ℕ) (h1 : 843 ≤ k) (h2 : k < 844) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 843 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf843_ok
theorem cr_844_845 (k : ℕ) (h1 : 844 ≤ k) (h2 : k < 845) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 844 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf844_ok
theorem cr_843_845 (k : ℕ) (h1 : 843 ≤ k) (h2 : k < 845) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 844 then cr_843_844 k h1 h else cr_844_845 k (by omega) h2
theorem cr_842_845 (k : ℕ) (h1 : 842 ≤ k) (h2 : k < 845) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 843 then cr_842_843 k h1 h else cr_843_845 k (by omega) h2
theorem cr_840_845 (k : ℕ) (h1 : 840 ≤ k) (h2 : k < 845) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 842 then cr_840_842 k h1 h else cr_842_845 k (by omega) h2
theorem cr_845_846 (k : ℕ) (h1 : 845 ≤ k) (h2 : k < 846) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 845 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf845_ok
theorem cr_846_847 (k : ℕ) (h1 : 846 ≤ k) (h2 : k < 847) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 846 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf846_ok
theorem cr_845_847 (k : ℕ) (h1 : 845 ≤ k) (h2 : k < 847) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 846 then cr_845_846 k h1 h else cr_846_847 k (by omega) h2
theorem cr_847_848 (k : ℕ) (h1 : 847 ≤ k) (h2 : k < 848) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 847 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf847_ok
theorem cr_848_849 (k : ℕ) (h1 : 848 ≤ k) (h2 : k < 849) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 848 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf848_ok
theorem cr_849_850 (k : ℕ) (h1 : 849 ≤ k) (h2 : k < 850) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 849 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf849_ok
theorem cr_848_850 (k : ℕ) (h1 : 848 ≤ k) (h2 : k < 850) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 849 then cr_848_849 k h1 h else cr_849_850 k (by omega) h2
theorem cr_847_850 (k : ℕ) (h1 : 847 ≤ k) (h2 : k < 850) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 848 then cr_847_848 k h1 h else cr_848_850 k (by omega) h2
theorem cr_845_850 (k : ℕ) (h1 : 845 ≤ k) (h2 : k < 850) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 847 then cr_845_847 k h1 h else cr_847_850 k (by omega) h2
theorem cr_840_850 (k : ℕ) (h1 : 840 ≤ k) (h2 : k < 850) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 845 then cr_840_845 k h1 h else cr_845_850 k (by omega) h2
theorem cr_850_851 (k : ℕ) (h1 : 850 ≤ k) (h2 : k < 851) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 850 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf850_ok
theorem cr_851_852 (k : ℕ) (h1 : 851 ≤ k) (h2 : k < 852) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 851 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf851_ok
theorem cr_850_852 (k : ℕ) (h1 : 850 ≤ k) (h2 : k < 852) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 851 then cr_850_851 k h1 h else cr_851_852 k (by omega) h2
theorem cr_852_853 (k : ℕ) (h1 : 852 ≤ k) (h2 : k < 853) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 852 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf852_ok
theorem cr_853_854 (k : ℕ) (h1 : 853 ≤ k) (h2 : k < 854) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 853 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf853_ok
theorem cr_854_855 (k : ℕ) (h1 : 854 ≤ k) (h2 : k < 855) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 854 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf854_ok
theorem cr_853_855 (k : ℕ) (h1 : 853 ≤ k) (h2 : k < 855) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 854 then cr_853_854 k h1 h else cr_854_855 k (by omega) h2
theorem cr_852_855 (k : ℕ) (h1 : 852 ≤ k) (h2 : k < 855) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 853 then cr_852_853 k h1 h else cr_853_855 k (by omega) h2
theorem cr_850_855 (k : ℕ) (h1 : 850 ≤ k) (h2 : k < 855) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 852 then cr_850_852 k h1 h else cr_852_855 k (by omega) h2
theorem cr_855_856 (k : ℕ) (h1 : 855 ≤ k) (h2 : k < 856) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 855 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf855_ok
theorem cr_856_857 (k : ℕ) (h1 : 856 ≤ k) (h2 : k < 857) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 856 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf856_ok
theorem cr_857_858 (k : ℕ) (h1 : 857 ≤ k) (h2 : k < 858) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 857 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf857_ok
theorem cr_856_858 (k : ℕ) (h1 : 856 ≤ k) (h2 : k < 858) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 857 then cr_856_857 k h1 h else cr_857_858 k (by omega) h2
theorem cr_855_858 (k : ℕ) (h1 : 855 ≤ k) (h2 : k < 858) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 856 then cr_855_856 k h1 h else cr_856_858 k (by omega) h2
theorem cr_858_859 (k : ℕ) (h1 : 858 ≤ k) (h2 : k < 859) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 858 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf858_ok
theorem cr_859_860 (k : ℕ) (h1 : 859 ≤ k) (h2 : k < 860) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 859 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf859_ok
theorem cr_860_861 (k : ℕ) (h1 : 860 ≤ k) (h2 : k < 861) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 860 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf860_ok
theorem cr_859_861 (k : ℕ) (h1 : 859 ≤ k) (h2 : k < 861) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 860 then cr_859_860 k h1 h else cr_860_861 k (by omega) h2
theorem cr_858_861 (k : ℕ) (h1 : 858 ≤ k) (h2 : k < 861) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 859 then cr_858_859 k h1 h else cr_859_861 k (by omega) h2
theorem cr_855_861 (k : ℕ) (h1 : 855 ≤ k) (h2 : k < 861) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 858 then cr_855_858 k h1 h else cr_858_861 k (by omega) h2
theorem cr_850_861 (k : ℕ) (h1 : 850 ≤ k) (h2 : k < 861) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 855 then cr_850_855 k h1 h else cr_855_861 k (by omega) h2
theorem cr_840_861 (k : ℕ) (h1 : 840 ≤ k) (h2 : k < 861) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 850 then cr_840_850 k h1 h else cr_850_861 k (by omega) h2
theorem cr_820_861 (k : ℕ) (h1 : 820 ≤ k) (h2 : k < 861) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 840 then cr_820_840 k h1 h else cr_840_861 k (by omega) h2
theorem cr_861_862 (k : ℕ) (h1 : 861 ≤ k) (h2 : k < 862) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 861 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf861_ok
theorem cr_862_863 (k : ℕ) (h1 : 862 ≤ k) (h2 : k < 863) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 862 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf862_ok
theorem cr_861_863 (k : ℕ) (h1 : 861 ≤ k) (h2 : k < 863) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 862 then cr_861_862 k h1 h else cr_862_863 k (by omega) h2
theorem cr_863_864 (k : ℕ) (h1 : 863 ≤ k) (h2 : k < 864) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 863 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf863_ok
theorem cr_864_865 (k : ℕ) (h1 : 864 ≤ k) (h2 : k < 865) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 864 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf864_ok
theorem cr_865_866 (k : ℕ) (h1 : 865 ≤ k) (h2 : k < 866) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 865 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf865_ok
theorem cr_864_866 (k : ℕ) (h1 : 864 ≤ k) (h2 : k < 866) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 865 then cr_864_865 k h1 h else cr_865_866 k (by omega) h2
theorem cr_863_866 (k : ℕ) (h1 : 863 ≤ k) (h2 : k < 866) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 864 then cr_863_864 k h1 h else cr_864_866 k (by omega) h2
theorem cr_861_866 (k : ℕ) (h1 : 861 ≤ k) (h2 : k < 866) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 863 then cr_861_863 k h1 h else cr_863_866 k (by omega) h2
theorem cr_866_867 (k : ℕ) (h1 : 866 ≤ k) (h2 : k < 867) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 866 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf866_ok
theorem cr_867_868 (k : ℕ) (h1 : 867 ≤ k) (h2 : k < 868) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 867 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf867_ok
theorem cr_866_868 (k : ℕ) (h1 : 866 ≤ k) (h2 : k < 868) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 867 then cr_866_867 k h1 h else cr_867_868 k (by omega) h2
theorem cr_868_869 (k : ℕ) (h1 : 868 ≤ k) (h2 : k < 869) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 868 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf868_ok
theorem cr_869_870 (k : ℕ) (h1 : 869 ≤ k) (h2 : k < 870) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 869 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf869_ok
theorem cr_870_871 (k : ℕ) (h1 : 870 ≤ k) (h2 : k < 871) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 870 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf870_ok
theorem cr_869_871 (k : ℕ) (h1 : 869 ≤ k) (h2 : k < 871) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 870 then cr_869_870 k h1 h else cr_870_871 k (by omega) h2
theorem cr_868_871 (k : ℕ) (h1 : 868 ≤ k) (h2 : k < 871) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 869 then cr_868_869 k h1 h else cr_869_871 k (by omega) h2
theorem cr_866_871 (k : ℕ) (h1 : 866 ≤ k) (h2 : k < 871) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 868 then cr_866_868 k h1 h else cr_868_871 k (by omega) h2
theorem cr_861_871 (k : ℕ) (h1 : 861 ≤ k) (h2 : k < 871) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 866 then cr_861_866 k h1 h else cr_866_871 k (by omega) h2
theorem cr_871_872 (k : ℕ) (h1 : 871 ≤ k) (h2 : k < 872) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 871 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf871_ok
theorem cr_872_873 (k : ℕ) (h1 : 872 ≤ k) (h2 : k < 873) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 872 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf872_ok
theorem cr_871_873 (k : ℕ) (h1 : 871 ≤ k) (h2 : k < 873) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 872 then cr_871_872 k h1 h else cr_872_873 k (by omega) h2
theorem cr_873_874 (k : ℕ) (h1 : 873 ≤ k) (h2 : k < 874) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 873 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf873_ok
theorem cr_874_875 (k : ℕ) (h1 : 874 ≤ k) (h2 : k < 875) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 874 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf874_ok
theorem cr_875_876 (k : ℕ) (h1 : 875 ≤ k) (h2 : k < 876) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 875 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf875_ok
theorem cr_874_876 (k : ℕ) (h1 : 874 ≤ k) (h2 : k < 876) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 875 then cr_874_875 k h1 h else cr_875_876 k (by omega) h2
theorem cr_873_876 (k : ℕ) (h1 : 873 ≤ k) (h2 : k < 876) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 874 then cr_873_874 k h1 h else cr_874_876 k (by omega) h2
theorem cr_871_876 (k : ℕ) (h1 : 871 ≤ k) (h2 : k < 876) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 873 then cr_871_873 k h1 h else cr_873_876 k (by omega) h2
theorem cr_876_877 (k : ℕ) (h1 : 876 ≤ k) (h2 : k < 877) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 876 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf876_ok
theorem cr_877_878 (k : ℕ) (h1 : 877 ≤ k) (h2 : k < 878) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 877 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf877_ok
theorem cr_876_878 (k : ℕ) (h1 : 876 ≤ k) (h2 : k < 878) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 877 then cr_876_877 k h1 h else cr_877_878 k (by omega) h2
theorem cr_878_879 (k : ℕ) (h1 : 878 ≤ k) (h2 : k < 879) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 878 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf878_ok
theorem cr_879_880 (k : ℕ) (h1 : 879 ≤ k) (h2 : k < 880) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 879 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf879_ok
theorem cr_880_881 (k : ℕ) (h1 : 880 ≤ k) (h2 : k < 881) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 880 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf880_ok
theorem cr_879_881 (k : ℕ) (h1 : 879 ≤ k) (h2 : k < 881) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 880 then cr_879_880 k h1 h else cr_880_881 k (by omega) h2
theorem cr_878_881 (k : ℕ) (h1 : 878 ≤ k) (h2 : k < 881) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 879 then cr_878_879 k h1 h else cr_879_881 k (by omega) h2
theorem cr_876_881 (k : ℕ) (h1 : 876 ≤ k) (h2 : k < 881) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 878 then cr_876_878 k h1 h else cr_878_881 k (by omega) h2
theorem cr_871_881 (k : ℕ) (h1 : 871 ≤ k) (h2 : k < 881) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 876 then cr_871_876 k h1 h else cr_876_881 k (by omega) h2
theorem cr_861_881 (k : ℕ) (h1 : 861 ≤ k) (h2 : k < 881) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 871 then cr_861_871 k h1 h else cr_871_881 k (by omega) h2
theorem cr_881_882 (k : ℕ) (h1 : 881 ≤ k) (h2 : k < 882) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 881 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf881_ok
theorem cr_882_883 (k : ℕ) (h1 : 882 ≤ k) (h2 : k < 883) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 882 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf882_ok
theorem cr_881_883 (k : ℕ) (h1 : 881 ≤ k) (h2 : k < 883) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 882 then cr_881_882 k h1 h else cr_882_883 k (by omega) h2
theorem cr_883_884 (k : ℕ) (h1 : 883 ≤ k) (h2 : k < 884) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 883 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf883_ok
theorem cr_884_885 (k : ℕ) (h1 : 884 ≤ k) (h2 : k < 885) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 884 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf884_ok
theorem cr_885_886 (k : ℕ) (h1 : 885 ≤ k) (h2 : k < 886) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 885 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf885_ok
theorem cr_884_886 (k : ℕ) (h1 : 884 ≤ k) (h2 : k < 886) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 885 then cr_884_885 k h1 h else cr_885_886 k (by omega) h2
theorem cr_883_886 (k : ℕ) (h1 : 883 ≤ k) (h2 : k < 886) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 884 then cr_883_884 k h1 h else cr_884_886 k (by omega) h2
theorem cr_881_886 (k : ℕ) (h1 : 881 ≤ k) (h2 : k < 886) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 883 then cr_881_883 k h1 h else cr_883_886 k (by omega) h2
theorem cr_886_887 (k : ℕ) (h1 : 886 ≤ k) (h2 : k < 887) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 886 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf886_ok
theorem cr_887_888 (k : ℕ) (h1 : 887 ≤ k) (h2 : k < 888) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 887 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf887_ok
theorem cr_886_888 (k : ℕ) (h1 : 886 ≤ k) (h2 : k < 888) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 887 then cr_886_887 k h1 h else cr_887_888 k (by omega) h2
theorem cr_888_889 (k : ℕ) (h1 : 888 ≤ k) (h2 : k < 889) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 888 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf888_ok
theorem cr_889_890 (k : ℕ) (h1 : 889 ≤ k) (h2 : k < 890) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 889 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf889_ok
theorem cr_890_891 (k : ℕ) (h1 : 890 ≤ k) (h2 : k < 891) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 890 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf890_ok
theorem cr_889_891 (k : ℕ) (h1 : 889 ≤ k) (h2 : k < 891) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 890 then cr_889_890 k h1 h else cr_890_891 k (by omega) h2
theorem cr_888_891 (k : ℕ) (h1 : 888 ≤ k) (h2 : k < 891) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 889 then cr_888_889 k h1 h else cr_889_891 k (by omega) h2
theorem cr_886_891 (k : ℕ) (h1 : 886 ≤ k) (h2 : k < 891) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 888 then cr_886_888 k h1 h else cr_888_891 k (by omega) h2
theorem cr_881_891 (k : ℕ) (h1 : 881 ≤ k) (h2 : k < 891) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 886 then cr_881_886 k h1 h else cr_886_891 k (by omega) h2
theorem cr_891_892 (k : ℕ) (h1 : 891 ≤ k) (h2 : k < 892) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 891 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf891_ok
theorem cr_892_893 (k : ℕ) (h1 : 892 ≤ k) (h2 : k < 893) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 892 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf892_ok
theorem cr_891_893 (k : ℕ) (h1 : 891 ≤ k) (h2 : k < 893) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 892 then cr_891_892 k h1 h else cr_892_893 k (by omega) h2
theorem cr_893_894 (k : ℕ) (h1 : 893 ≤ k) (h2 : k < 894) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 893 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf893_ok
theorem cr_894_895 (k : ℕ) (h1 : 894 ≤ k) (h2 : k < 895) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 894 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf894_ok
theorem cr_895_896 (k : ℕ) (h1 : 895 ≤ k) (h2 : k < 896) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 895 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf895_ok
theorem cr_894_896 (k : ℕ) (h1 : 894 ≤ k) (h2 : k < 896) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 895 then cr_894_895 k h1 h else cr_895_896 k (by omega) h2
theorem cr_893_896 (k : ℕ) (h1 : 893 ≤ k) (h2 : k < 896) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 894 then cr_893_894 k h1 h else cr_894_896 k (by omega) h2
theorem cr_891_896 (k : ℕ) (h1 : 891 ≤ k) (h2 : k < 896) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 893 then cr_891_893 k h1 h else cr_893_896 k (by omega) h2
theorem cr_896_897 (k : ℕ) (h1 : 896 ≤ k) (h2 : k < 897) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 896 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf896_ok
theorem cr_897_898 (k : ℕ) (h1 : 897 ≤ k) (h2 : k < 898) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 897 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf897_ok
theorem cr_898_899 (k : ℕ) (h1 : 898 ≤ k) (h2 : k < 899) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 898 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf898_ok
theorem cr_897_899 (k : ℕ) (h1 : 897 ≤ k) (h2 : k < 899) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 898 then cr_897_898 k h1 h else cr_898_899 k (by omega) h2
theorem cr_896_899 (k : ℕ) (h1 : 896 ≤ k) (h2 : k < 899) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 897 then cr_896_897 k h1 h else cr_897_899 k (by omega) h2
theorem cr_899_900 (k : ℕ) (h1 : 899 ≤ k) (h2 : k < 900) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 899 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf899_ok
theorem cr_900_901 (k : ℕ) (h1 : 900 ≤ k) (h2 : k < 901) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 900 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf900_ok
theorem cr_901_902 (k : ℕ) (h1 : 901 ≤ k) (h2 : k < 902) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 901 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf901_ok
theorem cr_900_902 (k : ℕ) (h1 : 900 ≤ k) (h2 : k < 902) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 901 then cr_900_901 k h1 h else cr_901_902 k (by omega) h2
theorem cr_899_902 (k : ℕ) (h1 : 899 ≤ k) (h2 : k < 902) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 900 then cr_899_900 k h1 h else cr_900_902 k (by omega) h2
theorem cr_896_902 (k : ℕ) (h1 : 896 ≤ k) (h2 : k < 902) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 899 then cr_896_899 k h1 h else cr_899_902 k (by omega) h2
theorem cr_891_902 (k : ℕ) (h1 : 891 ≤ k) (h2 : k < 902) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 896 then cr_891_896 k h1 h else cr_896_902 k (by omega) h2
theorem cr_881_902 (k : ℕ) (h1 : 881 ≤ k) (h2 : k < 902) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 891 then cr_881_891 k h1 h else cr_891_902 k (by omega) h2
theorem cr_861_902 (k : ℕ) (h1 : 861 ≤ k) (h2 : k < 902) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 881 then cr_861_881 k h1 h else cr_881_902 k (by omega) h2
theorem cr_820_902 (k : ℕ) (h1 : 820 ≤ k) (h2 : k < 902) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 861 then cr_820_861 k h1 h else cr_861_902 k (by omega) h2
theorem cr_902_903 (k : ℕ) (h1 : 902 ≤ k) (h2 : k < 903) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 902 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf902_ok
theorem cr_903_904 (k : ℕ) (h1 : 903 ≤ k) (h2 : k < 904) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 903 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf903_ok
theorem cr_902_904 (k : ℕ) (h1 : 902 ≤ k) (h2 : k < 904) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 903 then cr_902_903 k h1 h else cr_903_904 k (by omega) h2
theorem cr_904_905 (k : ℕ) (h1 : 904 ≤ k) (h2 : k < 905) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 904 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf904_ok
theorem cr_905_906 (k : ℕ) (h1 : 905 ≤ k) (h2 : k < 906) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 905 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf905_ok
theorem cr_906_907 (k : ℕ) (h1 : 906 ≤ k) (h2 : k < 907) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 906 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf906_ok
theorem cr_905_907 (k : ℕ) (h1 : 905 ≤ k) (h2 : k < 907) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 906 then cr_905_906 k h1 h else cr_906_907 k (by omega) h2
theorem cr_904_907 (k : ℕ) (h1 : 904 ≤ k) (h2 : k < 907) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 905 then cr_904_905 k h1 h else cr_905_907 k (by omega) h2
theorem cr_902_907 (k : ℕ) (h1 : 902 ≤ k) (h2 : k < 907) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 904 then cr_902_904 k h1 h else cr_904_907 k (by omega) h2
theorem cr_907_908 (k : ℕ) (h1 : 907 ≤ k) (h2 : k < 908) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 907 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf907_ok
theorem cr_908_909 (k : ℕ) (h1 : 908 ≤ k) (h2 : k < 909) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 908 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf908_ok
theorem cr_907_909 (k : ℕ) (h1 : 907 ≤ k) (h2 : k < 909) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 908 then cr_907_908 k h1 h else cr_908_909 k (by omega) h2
theorem cr_909_910 (k : ℕ) (h1 : 909 ≤ k) (h2 : k < 910) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 909 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf909_ok
theorem cr_910_911 (k : ℕ) (h1 : 910 ≤ k) (h2 : k < 911) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 910 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf910_ok
theorem cr_911_912 (k : ℕ) (h1 : 911 ≤ k) (h2 : k < 912) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 911 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf911_ok
theorem cr_910_912 (k : ℕ) (h1 : 910 ≤ k) (h2 : k < 912) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 911 then cr_910_911 k h1 h else cr_911_912 k (by omega) h2
theorem cr_909_912 (k : ℕ) (h1 : 909 ≤ k) (h2 : k < 912) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 910 then cr_909_910 k h1 h else cr_910_912 k (by omega) h2
theorem cr_907_912 (k : ℕ) (h1 : 907 ≤ k) (h2 : k < 912) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 909 then cr_907_909 k h1 h else cr_909_912 k (by omega) h2
theorem cr_902_912 (k : ℕ) (h1 : 902 ≤ k) (h2 : k < 912) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 907 then cr_902_907 k h1 h else cr_907_912 k (by omega) h2
theorem cr_912_913 (k : ℕ) (h1 : 912 ≤ k) (h2 : k < 913) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 912 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf912_ok
theorem cr_913_914 (k : ℕ) (h1 : 913 ≤ k) (h2 : k < 914) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 913 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf913_ok
theorem cr_912_914 (k : ℕ) (h1 : 912 ≤ k) (h2 : k < 914) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 913 then cr_912_913 k h1 h else cr_913_914 k (by omega) h2
theorem cr_914_915 (k : ℕ) (h1 : 914 ≤ k) (h2 : k < 915) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 914 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf914_ok
theorem cr_915_916 (k : ℕ) (h1 : 915 ≤ k) (h2 : k < 916) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 915 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf915_ok
theorem cr_916_917 (k : ℕ) (h1 : 916 ≤ k) (h2 : k < 917) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 916 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf916_ok
theorem cr_915_917 (k : ℕ) (h1 : 915 ≤ k) (h2 : k < 917) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 916 then cr_915_916 k h1 h else cr_916_917 k (by omega) h2
theorem cr_914_917 (k : ℕ) (h1 : 914 ≤ k) (h2 : k < 917) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 915 then cr_914_915 k h1 h else cr_915_917 k (by omega) h2
theorem cr_912_917 (k : ℕ) (h1 : 912 ≤ k) (h2 : k < 917) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 914 then cr_912_914 k h1 h else cr_914_917 k (by omega) h2
theorem cr_917_918 (k : ℕ) (h1 : 917 ≤ k) (h2 : k < 918) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 917 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf917_ok
theorem cr_918_919 (k : ℕ) (h1 : 918 ≤ k) (h2 : k < 919) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 918 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf918_ok
theorem cr_917_919 (k : ℕ) (h1 : 917 ≤ k) (h2 : k < 919) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 918 then cr_917_918 k h1 h else cr_918_919 k (by omega) h2
theorem cr_919_920 (k : ℕ) (h1 : 919 ≤ k) (h2 : k < 920) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 919 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf919_ok
theorem cr_920_921 (k : ℕ) (h1 : 920 ≤ k) (h2 : k < 921) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 920 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf920_ok
theorem cr_921_922 (k : ℕ) (h1 : 921 ≤ k) (h2 : k < 922) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 921 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf921_ok
theorem cr_920_922 (k : ℕ) (h1 : 920 ≤ k) (h2 : k < 922) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 921 then cr_920_921 k h1 h else cr_921_922 k (by omega) h2
theorem cr_919_922 (k : ℕ) (h1 : 919 ≤ k) (h2 : k < 922) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 920 then cr_919_920 k h1 h else cr_920_922 k (by omega) h2
theorem cr_917_922 (k : ℕ) (h1 : 917 ≤ k) (h2 : k < 922) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 919 then cr_917_919 k h1 h else cr_919_922 k (by omega) h2
theorem cr_912_922 (k : ℕ) (h1 : 912 ≤ k) (h2 : k < 922) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 917 then cr_912_917 k h1 h else cr_917_922 k (by omega) h2
theorem cr_902_922 (k : ℕ) (h1 : 902 ≤ k) (h2 : k < 922) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 912 then cr_902_912 k h1 h else cr_912_922 k (by omega) h2
theorem cr_922_923 (k : ℕ) (h1 : 922 ≤ k) (h2 : k < 923) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 922 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf922_ok
theorem cr_923_924 (k : ℕ) (h1 : 923 ≤ k) (h2 : k < 924) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 923 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf923_ok
theorem cr_922_924 (k : ℕ) (h1 : 922 ≤ k) (h2 : k < 924) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 923 then cr_922_923 k h1 h else cr_923_924 k (by omega) h2
theorem cr_924_925 (k : ℕ) (h1 : 924 ≤ k) (h2 : k < 925) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 924 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf924_ok
theorem cr_925_926 (k : ℕ) (h1 : 925 ≤ k) (h2 : k < 926) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 925 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf925_ok
theorem cr_926_927 (k : ℕ) (h1 : 926 ≤ k) (h2 : k < 927) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 926 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf926_ok
theorem cr_925_927 (k : ℕ) (h1 : 925 ≤ k) (h2 : k < 927) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 926 then cr_925_926 k h1 h else cr_926_927 k (by omega) h2
theorem cr_924_927 (k : ℕ) (h1 : 924 ≤ k) (h2 : k < 927) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 925 then cr_924_925 k h1 h else cr_925_927 k (by omega) h2
theorem cr_922_927 (k : ℕ) (h1 : 922 ≤ k) (h2 : k < 927) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 924 then cr_922_924 k h1 h else cr_924_927 k (by omega) h2
theorem cr_927_928 (k : ℕ) (h1 : 927 ≤ k) (h2 : k < 928) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 927 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf927_ok
theorem cr_928_929 (k : ℕ) (h1 : 928 ≤ k) (h2 : k < 929) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 928 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf928_ok
theorem cr_927_929 (k : ℕ) (h1 : 927 ≤ k) (h2 : k < 929) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 928 then cr_927_928 k h1 h else cr_928_929 k (by omega) h2
theorem cr_929_930 (k : ℕ) (h1 : 929 ≤ k) (h2 : k < 930) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 929 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf929_ok
theorem cr_930_931 (k : ℕ) (h1 : 930 ≤ k) (h2 : k < 931) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 930 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf930_ok
theorem cr_931_932 (k : ℕ) (h1 : 931 ≤ k) (h2 : k < 932) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 931 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf931_ok
theorem cr_930_932 (k : ℕ) (h1 : 930 ≤ k) (h2 : k < 932) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 931 then cr_930_931 k h1 h else cr_931_932 k (by omega) h2
theorem cr_929_932 (k : ℕ) (h1 : 929 ≤ k) (h2 : k < 932) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 930 then cr_929_930 k h1 h else cr_930_932 k (by omega) h2
theorem cr_927_932 (k : ℕ) (h1 : 927 ≤ k) (h2 : k < 932) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 929 then cr_927_929 k h1 h else cr_929_932 k (by omega) h2
theorem cr_922_932 (k : ℕ) (h1 : 922 ≤ k) (h2 : k < 932) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 927 then cr_922_927 k h1 h else cr_927_932 k (by omega) h2
theorem cr_932_933 (k : ℕ) (h1 : 932 ≤ k) (h2 : k < 933) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 932 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf932_ok
theorem cr_933_934 (k : ℕ) (h1 : 933 ≤ k) (h2 : k < 934) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 933 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf933_ok
theorem cr_932_934 (k : ℕ) (h1 : 932 ≤ k) (h2 : k < 934) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 933 then cr_932_933 k h1 h else cr_933_934 k (by omega) h2
theorem cr_934_935 (k : ℕ) (h1 : 934 ≤ k) (h2 : k < 935) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 934 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf934_ok
theorem cr_935_936 (k : ℕ) (h1 : 935 ≤ k) (h2 : k < 936) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 935 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf935_ok
theorem cr_936_937 (k : ℕ) (h1 : 936 ≤ k) (h2 : k < 937) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 936 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf936_ok
theorem cr_935_937 (k : ℕ) (h1 : 935 ≤ k) (h2 : k < 937) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 936 then cr_935_936 k h1 h else cr_936_937 k (by omega) h2
theorem cr_934_937 (k : ℕ) (h1 : 934 ≤ k) (h2 : k < 937) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 935 then cr_934_935 k h1 h else cr_935_937 k (by omega) h2
theorem cr_932_937 (k : ℕ) (h1 : 932 ≤ k) (h2 : k < 937) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 934 then cr_932_934 k h1 h else cr_934_937 k (by omega) h2
theorem cr_937_938 (k : ℕ) (h1 : 937 ≤ k) (h2 : k < 938) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 937 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf937_ok
theorem cr_938_939 (k : ℕ) (h1 : 938 ≤ k) (h2 : k < 939) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 938 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf938_ok
theorem cr_939_940 (k : ℕ) (h1 : 939 ≤ k) (h2 : k < 940) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 939 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf939_ok
theorem cr_938_940 (k : ℕ) (h1 : 938 ≤ k) (h2 : k < 940) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 939 then cr_938_939 k h1 h else cr_939_940 k (by omega) h2
theorem cr_937_940 (k : ℕ) (h1 : 937 ≤ k) (h2 : k < 940) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 938 then cr_937_938 k h1 h else cr_938_940 k (by omega) h2
theorem cr_940_941 (k : ℕ) (h1 : 940 ≤ k) (h2 : k < 941) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 940 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf940_ok
theorem cr_941_942 (k : ℕ) (h1 : 941 ≤ k) (h2 : k < 942) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 941 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf941_ok
theorem cr_942_943 (k : ℕ) (h1 : 942 ≤ k) (h2 : k < 943) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 942 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf942_ok
theorem cr_941_943 (k : ℕ) (h1 : 941 ≤ k) (h2 : k < 943) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 942 then cr_941_942 k h1 h else cr_942_943 k (by omega) h2
theorem cr_940_943 (k : ℕ) (h1 : 940 ≤ k) (h2 : k < 943) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 941 then cr_940_941 k h1 h else cr_941_943 k (by omega) h2
theorem cr_937_943 (k : ℕ) (h1 : 937 ≤ k) (h2 : k < 943) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 940 then cr_937_940 k h1 h else cr_940_943 k (by omega) h2
theorem cr_932_943 (k : ℕ) (h1 : 932 ≤ k) (h2 : k < 943) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 937 then cr_932_937 k h1 h else cr_937_943 k (by omega) h2
theorem cr_922_943 (k : ℕ) (h1 : 922 ≤ k) (h2 : k < 943) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 932 then cr_922_932 k h1 h else cr_932_943 k (by omega) h2
theorem cr_902_943 (k : ℕ) (h1 : 902 ≤ k) (h2 : k < 943) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 922 then cr_902_922 k h1 h else cr_922_943 k (by omega) h2
theorem cr_943_944 (k : ℕ) (h1 : 943 ≤ k) (h2 : k < 944) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 943 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf943_ok
theorem cr_944_945 (k : ℕ) (h1 : 944 ≤ k) (h2 : k < 945) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 944 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf944_ok
theorem cr_943_945 (k : ℕ) (h1 : 943 ≤ k) (h2 : k < 945) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 944 then cr_943_944 k h1 h else cr_944_945 k (by omega) h2
theorem cr_945_946 (k : ℕ) (h1 : 945 ≤ k) (h2 : k < 946) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 945 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf945_ok
theorem cr_946_947 (k : ℕ) (h1 : 946 ≤ k) (h2 : k < 947) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 946 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf946_ok
theorem cr_947_948 (k : ℕ) (h1 : 947 ≤ k) (h2 : k < 948) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 947 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf947_ok
theorem cr_946_948 (k : ℕ) (h1 : 946 ≤ k) (h2 : k < 948) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 947 then cr_946_947 k h1 h else cr_947_948 k (by omega) h2
theorem cr_945_948 (k : ℕ) (h1 : 945 ≤ k) (h2 : k < 948) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 946 then cr_945_946 k h1 h else cr_946_948 k (by omega) h2
theorem cr_943_948 (k : ℕ) (h1 : 943 ≤ k) (h2 : k < 948) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 945 then cr_943_945 k h1 h else cr_945_948 k (by omega) h2
theorem cr_948_949 (k : ℕ) (h1 : 948 ≤ k) (h2 : k < 949) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 948 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf948_ok
theorem cr_949_950 (k : ℕ) (h1 : 949 ≤ k) (h2 : k < 950) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 949 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf949_ok
theorem cr_948_950 (k : ℕ) (h1 : 948 ≤ k) (h2 : k < 950) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 949 then cr_948_949 k h1 h else cr_949_950 k (by omega) h2
theorem cr_950_951 (k : ℕ) (h1 : 950 ≤ k) (h2 : k < 951) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 950 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf950_ok
theorem cr_951_952 (k : ℕ) (h1 : 951 ≤ k) (h2 : k < 952) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 951 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf951_ok
theorem cr_952_953 (k : ℕ) (h1 : 952 ≤ k) (h2 : k < 953) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 952 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf952_ok
theorem cr_951_953 (k : ℕ) (h1 : 951 ≤ k) (h2 : k < 953) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 952 then cr_951_952 k h1 h else cr_952_953 k (by omega) h2
theorem cr_950_953 (k : ℕ) (h1 : 950 ≤ k) (h2 : k < 953) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 951 then cr_950_951 k h1 h else cr_951_953 k (by omega) h2
theorem cr_948_953 (k : ℕ) (h1 : 948 ≤ k) (h2 : k < 953) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 950 then cr_948_950 k h1 h else cr_950_953 k (by omega) h2
theorem cr_943_953 (k : ℕ) (h1 : 943 ≤ k) (h2 : k < 953) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 948 then cr_943_948 k h1 h else cr_948_953 k (by omega) h2
theorem cr_953_954 (k : ℕ) (h1 : 953 ≤ k) (h2 : k < 954) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 953 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf953_ok
theorem cr_954_955 (k : ℕ) (h1 : 954 ≤ k) (h2 : k < 955) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 954 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf954_ok
theorem cr_953_955 (k : ℕ) (h1 : 953 ≤ k) (h2 : k < 955) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 954 then cr_953_954 k h1 h else cr_954_955 k (by omega) h2
theorem cr_955_956 (k : ℕ) (h1 : 955 ≤ k) (h2 : k < 956) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 955 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf955_ok
theorem cr_956_957 (k : ℕ) (h1 : 956 ≤ k) (h2 : k < 957) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 956 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf956_ok
theorem cr_957_958 (k : ℕ) (h1 : 957 ≤ k) (h2 : k < 958) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 957 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf957_ok
theorem cr_956_958 (k : ℕ) (h1 : 956 ≤ k) (h2 : k < 958) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 957 then cr_956_957 k h1 h else cr_957_958 k (by omega) h2
theorem cr_955_958 (k : ℕ) (h1 : 955 ≤ k) (h2 : k < 958) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 956 then cr_955_956 k h1 h else cr_956_958 k (by omega) h2
theorem cr_953_958 (k : ℕ) (h1 : 953 ≤ k) (h2 : k < 958) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 955 then cr_953_955 k h1 h else cr_955_958 k (by omega) h2
theorem cr_958_959 (k : ℕ) (h1 : 958 ≤ k) (h2 : k < 959) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 958 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf958_ok
theorem cr_959_960 (k : ℕ) (h1 : 959 ≤ k) (h2 : k < 960) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 959 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf959_ok
theorem cr_958_960 (k : ℕ) (h1 : 958 ≤ k) (h2 : k < 960) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 959 then cr_958_959 k h1 h else cr_959_960 k (by omega) h2
theorem cr_960_961 (k : ℕ) (h1 : 960 ≤ k) (h2 : k < 961) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 960 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf960_ok
theorem cr_961_962 (k : ℕ) (h1 : 961 ≤ k) (h2 : k < 962) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 961 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf961_ok
theorem cr_962_963 (k : ℕ) (h1 : 962 ≤ k) (h2 : k < 963) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 962 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf962_ok
theorem cr_961_963 (k : ℕ) (h1 : 961 ≤ k) (h2 : k < 963) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 962 then cr_961_962 k h1 h else cr_962_963 k (by omega) h2
theorem cr_960_963 (k : ℕ) (h1 : 960 ≤ k) (h2 : k < 963) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 961 then cr_960_961 k h1 h else cr_961_963 k (by omega) h2
theorem cr_958_963 (k : ℕ) (h1 : 958 ≤ k) (h2 : k < 963) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 960 then cr_958_960 k h1 h else cr_960_963 k (by omega) h2
theorem cr_953_963 (k : ℕ) (h1 : 953 ≤ k) (h2 : k < 963) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 958 then cr_953_958 k h1 h else cr_958_963 k (by omega) h2
theorem cr_943_963 (k : ℕ) (h1 : 943 ≤ k) (h2 : k < 963) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 953 then cr_943_953 k h1 h else cr_953_963 k (by omega) h2
theorem cr_963_964 (k : ℕ) (h1 : 963 ≤ k) (h2 : k < 964) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 963 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf963_ok
theorem cr_964_965 (k : ℕ) (h1 : 964 ≤ k) (h2 : k < 965) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 964 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf964_ok
theorem cr_963_965 (k : ℕ) (h1 : 963 ≤ k) (h2 : k < 965) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 964 then cr_963_964 k h1 h else cr_964_965 k (by omega) h2
theorem cr_965_966 (k : ℕ) (h1 : 965 ≤ k) (h2 : k < 966) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 965 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf965_ok
theorem cr_966_967 (k : ℕ) (h1 : 966 ≤ k) (h2 : k < 967) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 966 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf966_ok
theorem cr_967_968 (k : ℕ) (h1 : 967 ≤ k) (h2 : k < 968) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 967 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf967_ok
theorem cr_966_968 (k : ℕ) (h1 : 966 ≤ k) (h2 : k < 968) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 967 then cr_966_967 k h1 h else cr_967_968 k (by omega) h2
theorem cr_965_968 (k : ℕ) (h1 : 965 ≤ k) (h2 : k < 968) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 966 then cr_965_966 k h1 h else cr_966_968 k (by omega) h2
theorem cr_963_968 (k : ℕ) (h1 : 963 ≤ k) (h2 : k < 968) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 965 then cr_963_965 k h1 h else cr_965_968 k (by omega) h2
theorem cr_968_969 (k : ℕ) (h1 : 968 ≤ k) (h2 : k < 969) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 968 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf968_ok
theorem cr_969_970 (k : ℕ) (h1 : 969 ≤ k) (h2 : k < 970) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 969 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf969_ok
theorem cr_968_970 (k : ℕ) (h1 : 968 ≤ k) (h2 : k < 970) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 969 then cr_968_969 k h1 h else cr_969_970 k (by omega) h2
theorem cr_970_971 (k : ℕ) (h1 : 970 ≤ k) (h2 : k < 971) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 970 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf970_ok
theorem cr_971_972 (k : ℕ) (h1 : 971 ≤ k) (h2 : k < 972) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 971 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf971_ok
theorem cr_972_973 (k : ℕ) (h1 : 972 ≤ k) (h2 : k < 973) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 972 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf972_ok
theorem cr_971_973 (k : ℕ) (h1 : 971 ≤ k) (h2 : k < 973) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 972 then cr_971_972 k h1 h else cr_972_973 k (by omega) h2
theorem cr_970_973 (k : ℕ) (h1 : 970 ≤ k) (h2 : k < 973) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 971 then cr_970_971 k h1 h else cr_971_973 k (by omega) h2
theorem cr_968_973 (k : ℕ) (h1 : 968 ≤ k) (h2 : k < 973) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 970 then cr_968_970 k h1 h else cr_970_973 k (by omega) h2
theorem cr_963_973 (k : ℕ) (h1 : 963 ≤ k) (h2 : k < 973) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 968 then cr_963_968 k h1 h else cr_968_973 k (by omega) h2
theorem cr_973_974 (k : ℕ) (h1 : 973 ≤ k) (h2 : k < 974) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 973 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf973_ok
theorem cr_974_975 (k : ℕ) (h1 : 974 ≤ k) (h2 : k < 975) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 974 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf974_ok
theorem cr_973_975 (k : ℕ) (h1 : 973 ≤ k) (h2 : k < 975) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 974 then cr_973_974 k h1 h else cr_974_975 k (by omega) h2
theorem cr_975_976 (k : ℕ) (h1 : 975 ≤ k) (h2 : k < 976) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 975 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf975_ok
theorem cr_976_977 (k : ℕ) (h1 : 976 ≤ k) (h2 : k < 977) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 976 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf976_ok
theorem cr_977_978 (k : ℕ) (h1 : 977 ≤ k) (h2 : k < 978) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 977 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf977_ok
theorem cr_976_978 (k : ℕ) (h1 : 976 ≤ k) (h2 : k < 978) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 977 then cr_976_977 k h1 h else cr_977_978 k (by omega) h2
theorem cr_975_978 (k : ℕ) (h1 : 975 ≤ k) (h2 : k < 978) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 976 then cr_975_976 k h1 h else cr_976_978 k (by omega) h2
theorem cr_973_978 (k : ℕ) (h1 : 973 ≤ k) (h2 : k < 978) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 975 then cr_973_975 k h1 h else cr_975_978 k (by omega) h2
theorem cr_978_979 (k : ℕ) (h1 : 978 ≤ k) (h2 : k < 979) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 978 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf978_ok
theorem cr_979_980 (k : ℕ) (h1 : 979 ≤ k) (h2 : k < 980) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 979 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf979_ok
theorem cr_980_981 (k : ℕ) (h1 : 980 ≤ k) (h2 : k < 981) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 980 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf980_ok
theorem cr_979_981 (k : ℕ) (h1 : 979 ≤ k) (h2 : k < 981) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 980 then cr_979_980 k h1 h else cr_980_981 k (by omega) h2
theorem cr_978_981 (k : ℕ) (h1 : 978 ≤ k) (h2 : k < 981) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 979 then cr_978_979 k h1 h else cr_979_981 k (by omega) h2
theorem cr_981_982 (k : ℕ) (h1 : 981 ≤ k) (h2 : k < 982) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 981 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf981_ok
theorem cr_982_983 (k : ℕ) (h1 : 982 ≤ k) (h2 : k < 983) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 982 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf982_ok
theorem cr_983_984 (k : ℕ) (h1 : 983 ≤ k) (h2 : k < 984) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 983 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf983_ok
theorem cr_982_984 (k : ℕ) (h1 : 982 ≤ k) (h2 : k < 984) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 983 then cr_982_983 k h1 h else cr_983_984 k (by omega) h2
theorem cr_981_984 (k : ℕ) (h1 : 981 ≤ k) (h2 : k < 984) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 982 then cr_981_982 k h1 h else cr_982_984 k (by omega) h2
theorem cr_978_984 (k : ℕ) (h1 : 978 ≤ k) (h2 : k < 984) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 981 then cr_978_981 k h1 h else cr_981_984 k (by omega) h2
theorem cr_973_984 (k : ℕ) (h1 : 973 ≤ k) (h2 : k < 984) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 978 then cr_973_978 k h1 h else cr_978_984 k (by omega) h2
theorem cr_963_984 (k : ℕ) (h1 : 963 ≤ k) (h2 : k < 984) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 973 then cr_963_973 k h1 h else cr_973_984 k (by omega) h2
theorem cr_943_984 (k : ℕ) (h1 : 943 ≤ k) (h2 : k < 984) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 963 then cr_943_963 k h1 h else cr_963_984 k (by omega) h2
theorem cr_902_984 (k : ℕ) (h1 : 902 ≤ k) (h2 : k < 984) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 943 then cr_902_943 k h1 h else cr_943_984 k (by omega) h2
theorem cr_820_984 (k : ℕ) (h1 : 820 ≤ k) (h2 : k < 984) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 902 then cr_820_902 k h1 h else cr_902_984 k (by omega) h2
theorem cr_656_984 (k : ℕ) (h1 : 656 ≤ k) (h2 : k < 984) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 820 then cr_656_820 k h1 h else cr_820_984 k (by omega) h2
theorem cr_984_985 (k : ℕ) (h1 : 984 ≤ k) (h2 : k < 985) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 984 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf984_ok
theorem cr_985_986 (k : ℕ) (h1 : 985 ≤ k) (h2 : k < 986) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 985 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf985_ok
theorem cr_984_986 (k : ℕ) (h1 : 984 ≤ k) (h2 : k < 986) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 985 then cr_984_985 k h1 h else cr_985_986 k (by omega) h2
theorem cr_986_987 (k : ℕ) (h1 : 986 ≤ k) (h2 : k < 987) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 986 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf986_ok
theorem cr_987_988 (k : ℕ) (h1 : 987 ≤ k) (h2 : k < 988) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 987 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf987_ok
theorem cr_988_989 (k : ℕ) (h1 : 988 ≤ k) (h2 : k < 989) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 988 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf988_ok
theorem cr_987_989 (k : ℕ) (h1 : 987 ≤ k) (h2 : k < 989) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 988 then cr_987_988 k h1 h else cr_988_989 k (by omega) h2
theorem cr_986_989 (k : ℕ) (h1 : 986 ≤ k) (h2 : k < 989) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 987 then cr_986_987 k h1 h else cr_987_989 k (by omega) h2
theorem cr_984_989 (k : ℕ) (h1 : 984 ≤ k) (h2 : k < 989) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 986 then cr_984_986 k h1 h else cr_986_989 k (by omega) h2
theorem cr_989_990 (k : ℕ) (h1 : 989 ≤ k) (h2 : k < 990) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 989 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf989_ok
theorem cr_990_991 (k : ℕ) (h1 : 990 ≤ k) (h2 : k < 991) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 990 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf990_ok
theorem cr_989_991 (k : ℕ) (h1 : 989 ≤ k) (h2 : k < 991) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 990 then cr_989_990 k h1 h else cr_990_991 k (by omega) h2
theorem cr_991_992 (k : ℕ) (h1 : 991 ≤ k) (h2 : k < 992) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 991 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf991_ok
theorem cr_992_993 (k : ℕ) (h1 : 992 ≤ k) (h2 : k < 993) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 992 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf992_ok
theorem cr_993_994 (k : ℕ) (h1 : 993 ≤ k) (h2 : k < 994) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 993 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf993_ok
theorem cr_992_994 (k : ℕ) (h1 : 992 ≤ k) (h2 : k < 994) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 993 then cr_992_993 k h1 h else cr_993_994 k (by omega) h2
theorem cr_991_994 (k : ℕ) (h1 : 991 ≤ k) (h2 : k < 994) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 992 then cr_991_992 k h1 h else cr_992_994 k (by omega) h2
theorem cr_989_994 (k : ℕ) (h1 : 989 ≤ k) (h2 : k < 994) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 991 then cr_989_991 k h1 h else cr_991_994 k (by omega) h2
theorem cr_984_994 (k : ℕ) (h1 : 984 ≤ k) (h2 : k < 994) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 989 then cr_984_989 k h1 h else cr_989_994 k (by omega) h2
theorem cr_994_995 (k : ℕ) (h1 : 994 ≤ k) (h2 : k < 995) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 994 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf994_ok
theorem cr_995_996 (k : ℕ) (h1 : 995 ≤ k) (h2 : k < 996) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 995 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf995_ok
theorem cr_994_996 (k : ℕ) (h1 : 994 ≤ k) (h2 : k < 996) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 995 then cr_994_995 k h1 h else cr_995_996 k (by omega) h2
theorem cr_996_997 (k : ℕ) (h1 : 996 ≤ k) (h2 : k < 997) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 996 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf996_ok
theorem cr_997_998 (k : ℕ) (h1 : 997 ≤ k) (h2 : k < 998) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 997 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf997_ok
theorem cr_998_999 (k : ℕ) (h1 : 998 ≤ k) (h2 : k < 999) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 998 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf998_ok
theorem cr_997_999 (k : ℕ) (h1 : 997 ≤ k) (h2 : k < 999) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 998 then cr_997_998 k h1 h else cr_998_999 k (by omega) h2
theorem cr_996_999 (k : ℕ) (h1 : 996 ≤ k) (h2 : k < 999) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 997 then cr_996_997 k h1 h else cr_997_999 k (by omega) h2
theorem cr_994_999 (k : ℕ) (h1 : 994 ≤ k) (h2 : k < 999) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 996 then cr_994_996 k h1 h else cr_996_999 k (by omega) h2
theorem cr_999_1000 (k : ℕ) (h1 : 999 ≤ k) (h2 : k < 1000) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 999 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf999_ok
theorem cr_1000_1001 (k : ℕ) (h1 : 1000 ≤ k) (h2 : k < 1001) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1000 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1000_ok
theorem cr_999_1001 (k : ℕ) (h1 : 999 ≤ k) (h2 : k < 1001) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1000 then cr_999_1000 k h1 h else cr_1000_1001 k (by omega) h2
theorem cr_1001_1002 (k : ℕ) (h1 : 1001 ≤ k) (h2 : k < 1002) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1001 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1001_ok
theorem cr_1002_1003 (k : ℕ) (h1 : 1002 ≤ k) (h2 : k < 1003) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1002 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1002_ok
theorem cr_1003_1004 (k : ℕ) (h1 : 1003 ≤ k) (h2 : k < 1004) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1003 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1003_ok
theorem cr_1002_1004 (k : ℕ) (h1 : 1002 ≤ k) (h2 : k < 1004) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1003 then cr_1002_1003 k h1 h else cr_1003_1004 k (by omega) h2
theorem cr_1001_1004 (k : ℕ) (h1 : 1001 ≤ k) (h2 : k < 1004) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1002 then cr_1001_1002 k h1 h else cr_1002_1004 k (by omega) h2
theorem cr_999_1004 (k : ℕ) (h1 : 999 ≤ k) (h2 : k < 1004) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1001 then cr_999_1001 k h1 h else cr_1001_1004 k (by omega) h2
theorem cr_994_1004 (k : ℕ) (h1 : 994 ≤ k) (h2 : k < 1004) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 999 then cr_994_999 k h1 h else cr_999_1004 k (by omega) h2
theorem cr_984_1004 (k : ℕ) (h1 : 984 ≤ k) (h2 : k < 1004) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 994 then cr_984_994 k h1 h else cr_994_1004 k (by omega) h2
theorem cr_1004_1005 (k : ℕ) (h1 : 1004 ≤ k) (h2 : k < 1005) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1004 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1004_ok
theorem cr_1005_1006 (k : ℕ) (h1 : 1005 ≤ k) (h2 : k < 1006) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1005 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1005_ok
theorem cr_1004_1006 (k : ℕ) (h1 : 1004 ≤ k) (h2 : k < 1006) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1005 then cr_1004_1005 k h1 h else cr_1005_1006 k (by omega) h2
theorem cr_1006_1007 (k : ℕ) (h1 : 1006 ≤ k) (h2 : k < 1007) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1006 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1006_ok
theorem cr_1007_1008 (k : ℕ) (h1 : 1007 ≤ k) (h2 : k < 1008) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1007 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1007_ok
theorem cr_1008_1009 (k : ℕ) (h1 : 1008 ≤ k) (h2 : k < 1009) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1008 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1008_ok
theorem cr_1007_1009 (k : ℕ) (h1 : 1007 ≤ k) (h2 : k < 1009) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1008 then cr_1007_1008 k h1 h else cr_1008_1009 k (by omega) h2
theorem cr_1006_1009 (k : ℕ) (h1 : 1006 ≤ k) (h2 : k < 1009) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1007 then cr_1006_1007 k h1 h else cr_1007_1009 k (by omega) h2
theorem cr_1004_1009 (k : ℕ) (h1 : 1004 ≤ k) (h2 : k < 1009) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1006 then cr_1004_1006 k h1 h else cr_1006_1009 k (by omega) h2
theorem cr_1009_1010 (k : ℕ) (h1 : 1009 ≤ k) (h2 : k < 1010) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1009 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1009_ok
theorem cr_1010_1011 (k : ℕ) (h1 : 1010 ≤ k) (h2 : k < 1011) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1010 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1010_ok
theorem cr_1009_1011 (k : ℕ) (h1 : 1009 ≤ k) (h2 : k < 1011) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1010 then cr_1009_1010 k h1 h else cr_1010_1011 k (by omega) h2
theorem cr_1011_1012 (k : ℕ) (h1 : 1011 ≤ k) (h2 : k < 1012) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1011 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1011_ok
theorem cr_1012_1013 (k : ℕ) (h1 : 1012 ≤ k) (h2 : k < 1013) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1012 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1012_ok
theorem cr_1013_1014 (k : ℕ) (h1 : 1013 ≤ k) (h2 : k < 1014) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1013 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1013_ok
theorem cr_1012_1014 (k : ℕ) (h1 : 1012 ≤ k) (h2 : k < 1014) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1013 then cr_1012_1013 k h1 h else cr_1013_1014 k (by omega) h2
theorem cr_1011_1014 (k : ℕ) (h1 : 1011 ≤ k) (h2 : k < 1014) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1012 then cr_1011_1012 k h1 h else cr_1012_1014 k (by omega) h2
theorem cr_1009_1014 (k : ℕ) (h1 : 1009 ≤ k) (h2 : k < 1014) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1011 then cr_1009_1011 k h1 h else cr_1011_1014 k (by omega) h2
theorem cr_1004_1014 (k : ℕ) (h1 : 1004 ≤ k) (h2 : k < 1014) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1009 then cr_1004_1009 k h1 h else cr_1009_1014 k (by omega) h2
theorem cr_1014_1015 (k : ℕ) (h1 : 1014 ≤ k) (h2 : k < 1015) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1014 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1014_ok
theorem cr_1015_1016 (k : ℕ) (h1 : 1015 ≤ k) (h2 : k < 1016) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1015 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1015_ok
theorem cr_1014_1016 (k : ℕ) (h1 : 1014 ≤ k) (h2 : k < 1016) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1015 then cr_1014_1015 k h1 h else cr_1015_1016 k (by omega) h2
theorem cr_1016_1017 (k : ℕ) (h1 : 1016 ≤ k) (h2 : k < 1017) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1016 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1016_ok
theorem cr_1017_1018 (k : ℕ) (h1 : 1017 ≤ k) (h2 : k < 1018) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1017 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1017_ok
theorem cr_1018_1019 (k : ℕ) (h1 : 1018 ≤ k) (h2 : k < 1019) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1018 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1018_ok
theorem cr_1017_1019 (k : ℕ) (h1 : 1017 ≤ k) (h2 : k < 1019) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1018 then cr_1017_1018 k h1 h else cr_1018_1019 k (by omega) h2
theorem cr_1016_1019 (k : ℕ) (h1 : 1016 ≤ k) (h2 : k < 1019) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1017 then cr_1016_1017 k h1 h else cr_1017_1019 k (by omega) h2
theorem cr_1014_1019 (k : ℕ) (h1 : 1014 ≤ k) (h2 : k < 1019) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1016 then cr_1014_1016 k h1 h else cr_1016_1019 k (by omega) h2
theorem cr_1019_1020 (k : ℕ) (h1 : 1019 ≤ k) (h2 : k < 1020) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1019 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1019_ok
theorem cr_1020_1021 (k : ℕ) (h1 : 1020 ≤ k) (h2 : k < 1021) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1020 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1020_ok
theorem cr_1021_1022 (k : ℕ) (h1 : 1021 ≤ k) (h2 : k < 1022) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1021 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1021_ok
theorem cr_1020_1022 (k : ℕ) (h1 : 1020 ≤ k) (h2 : k < 1022) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1021 then cr_1020_1021 k h1 h else cr_1021_1022 k (by omega) h2
theorem cr_1019_1022 (k : ℕ) (h1 : 1019 ≤ k) (h2 : k < 1022) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1020 then cr_1019_1020 k h1 h else cr_1020_1022 k (by omega) h2
theorem cr_1022_1023 (k : ℕ) (h1 : 1022 ≤ k) (h2 : k < 1023) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1022 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1022_ok
theorem cr_1023_1024 (k : ℕ) (h1 : 1023 ≤ k) (h2 : k < 1024) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1023 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1023_ok
theorem cr_1024_1025 (k : ℕ) (h1 : 1024 ≤ k) (h2 : k < 1025) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1024 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1024_ok
theorem cr_1023_1025 (k : ℕ) (h1 : 1023 ≤ k) (h2 : k < 1025) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1024 then cr_1023_1024 k h1 h else cr_1024_1025 k (by omega) h2
theorem cr_1022_1025 (k : ℕ) (h1 : 1022 ≤ k) (h2 : k < 1025) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1023 then cr_1022_1023 k h1 h else cr_1023_1025 k (by omega) h2
theorem cr_1019_1025 (k : ℕ) (h1 : 1019 ≤ k) (h2 : k < 1025) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1022 then cr_1019_1022 k h1 h else cr_1022_1025 k (by omega) h2
theorem cr_1014_1025 (k : ℕ) (h1 : 1014 ≤ k) (h2 : k < 1025) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1019 then cr_1014_1019 k h1 h else cr_1019_1025 k (by omega) h2
theorem cr_1004_1025 (k : ℕ) (h1 : 1004 ≤ k) (h2 : k < 1025) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1014 then cr_1004_1014 k h1 h else cr_1014_1025 k (by omega) h2
theorem cr_984_1025 (k : ℕ) (h1 : 984 ≤ k) (h2 : k < 1025) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1004 then cr_984_1004 k h1 h else cr_1004_1025 k (by omega) h2
theorem cr_1025_1026 (k : ℕ) (h1 : 1025 ≤ k) (h2 : k < 1026) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1025 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1025_ok
theorem cr_1026_1027 (k : ℕ) (h1 : 1026 ≤ k) (h2 : k < 1027) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1026 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1026_ok
theorem cr_1025_1027 (k : ℕ) (h1 : 1025 ≤ k) (h2 : k < 1027) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1026 then cr_1025_1026 k h1 h else cr_1026_1027 k (by omega) h2
theorem cr_1027_1028 (k : ℕ) (h1 : 1027 ≤ k) (h2 : k < 1028) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1027 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1027_ok
theorem cr_1028_1029 (k : ℕ) (h1 : 1028 ≤ k) (h2 : k < 1029) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1028 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1028_ok
theorem cr_1029_1030 (k : ℕ) (h1 : 1029 ≤ k) (h2 : k < 1030) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1029 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1029_ok
theorem cr_1028_1030 (k : ℕ) (h1 : 1028 ≤ k) (h2 : k < 1030) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1029 then cr_1028_1029 k h1 h else cr_1029_1030 k (by omega) h2
theorem cr_1027_1030 (k : ℕ) (h1 : 1027 ≤ k) (h2 : k < 1030) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1028 then cr_1027_1028 k h1 h else cr_1028_1030 k (by omega) h2
theorem cr_1025_1030 (k : ℕ) (h1 : 1025 ≤ k) (h2 : k < 1030) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1027 then cr_1025_1027 k h1 h else cr_1027_1030 k (by omega) h2
theorem cr_1030_1031 (k : ℕ) (h1 : 1030 ≤ k) (h2 : k < 1031) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1030 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1030_ok
theorem cr_1031_1032 (k : ℕ) (h1 : 1031 ≤ k) (h2 : k < 1032) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1031 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1031_ok
theorem cr_1030_1032 (k : ℕ) (h1 : 1030 ≤ k) (h2 : k < 1032) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1031 then cr_1030_1031 k h1 h else cr_1031_1032 k (by omega) h2
theorem cr_1032_1033 (k : ℕ) (h1 : 1032 ≤ k) (h2 : k < 1033) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1032 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1032_ok
theorem cr_1033_1034 (k : ℕ) (h1 : 1033 ≤ k) (h2 : k < 1034) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1033 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1033_ok
theorem cr_1034_1035 (k : ℕ) (h1 : 1034 ≤ k) (h2 : k < 1035) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1034 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1034_ok
theorem cr_1033_1035 (k : ℕ) (h1 : 1033 ≤ k) (h2 : k < 1035) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1034 then cr_1033_1034 k h1 h else cr_1034_1035 k (by omega) h2
theorem cr_1032_1035 (k : ℕ) (h1 : 1032 ≤ k) (h2 : k < 1035) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1033 then cr_1032_1033 k h1 h else cr_1033_1035 k (by omega) h2
theorem cr_1030_1035 (k : ℕ) (h1 : 1030 ≤ k) (h2 : k < 1035) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1032 then cr_1030_1032 k h1 h else cr_1032_1035 k (by omega) h2
theorem cr_1025_1035 (k : ℕ) (h1 : 1025 ≤ k) (h2 : k < 1035) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1030 then cr_1025_1030 k h1 h else cr_1030_1035 k (by omega) h2
theorem cr_1035_1036 (k : ℕ) (h1 : 1035 ≤ k) (h2 : k < 1036) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1035 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1035_ok
theorem cr_1036_1037 (k : ℕ) (h1 : 1036 ≤ k) (h2 : k < 1037) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1036 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1036_ok
theorem cr_1035_1037 (k : ℕ) (h1 : 1035 ≤ k) (h2 : k < 1037) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1036 then cr_1035_1036 k h1 h else cr_1036_1037 k (by omega) h2
theorem cr_1037_1038 (k : ℕ) (h1 : 1037 ≤ k) (h2 : k < 1038) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1037 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1037_ok
theorem cr_1038_1039 (k : ℕ) (h1 : 1038 ≤ k) (h2 : k < 1039) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1038 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1038_ok
theorem cr_1039_1040 (k : ℕ) (h1 : 1039 ≤ k) (h2 : k < 1040) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1039 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1039_ok
theorem cr_1038_1040 (k : ℕ) (h1 : 1038 ≤ k) (h2 : k < 1040) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1039 then cr_1038_1039 k h1 h else cr_1039_1040 k (by omega) h2
theorem cr_1037_1040 (k : ℕ) (h1 : 1037 ≤ k) (h2 : k < 1040) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1038 then cr_1037_1038 k h1 h else cr_1038_1040 k (by omega) h2
theorem cr_1035_1040 (k : ℕ) (h1 : 1035 ≤ k) (h2 : k < 1040) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1037 then cr_1035_1037 k h1 h else cr_1037_1040 k (by omega) h2
theorem cr_1040_1041 (k : ℕ) (h1 : 1040 ≤ k) (h2 : k < 1041) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1040 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1040_ok
theorem cr_1041_1042 (k : ℕ) (h1 : 1041 ≤ k) (h2 : k < 1042) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1041 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1041_ok
theorem cr_1040_1042 (k : ℕ) (h1 : 1040 ≤ k) (h2 : k < 1042) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1041 then cr_1040_1041 k h1 h else cr_1041_1042 k (by omega) h2
theorem cr_1042_1043 (k : ℕ) (h1 : 1042 ≤ k) (h2 : k < 1043) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1042 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1042_ok
theorem cr_1043_1044 (k : ℕ) (h1 : 1043 ≤ k) (h2 : k < 1044) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1043 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1043_ok
theorem cr_1044_1045 (k : ℕ) (h1 : 1044 ≤ k) (h2 : k < 1045) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1044 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1044_ok
theorem cr_1043_1045 (k : ℕ) (h1 : 1043 ≤ k) (h2 : k < 1045) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1044 then cr_1043_1044 k h1 h else cr_1044_1045 k (by omega) h2
theorem cr_1042_1045 (k : ℕ) (h1 : 1042 ≤ k) (h2 : k < 1045) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1043 then cr_1042_1043 k h1 h else cr_1043_1045 k (by omega) h2
theorem cr_1040_1045 (k : ℕ) (h1 : 1040 ≤ k) (h2 : k < 1045) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1042 then cr_1040_1042 k h1 h else cr_1042_1045 k (by omega) h2
theorem cr_1035_1045 (k : ℕ) (h1 : 1035 ≤ k) (h2 : k < 1045) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1040 then cr_1035_1040 k h1 h else cr_1040_1045 k (by omega) h2
theorem cr_1025_1045 (k : ℕ) (h1 : 1025 ≤ k) (h2 : k < 1045) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1035 then cr_1025_1035 k h1 h else cr_1035_1045 k (by omega) h2
theorem cr_1045_1046 (k : ℕ) (h1 : 1045 ≤ k) (h2 : k < 1046) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1045 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1045_ok
theorem cr_1046_1047 (k : ℕ) (h1 : 1046 ≤ k) (h2 : k < 1047) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1046 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1046_ok
theorem cr_1045_1047 (k : ℕ) (h1 : 1045 ≤ k) (h2 : k < 1047) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1046 then cr_1045_1046 k h1 h else cr_1046_1047 k (by omega) h2
theorem cr_1047_1048 (k : ℕ) (h1 : 1047 ≤ k) (h2 : k < 1048) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1047 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1047_ok
theorem cr_1048_1049 (k : ℕ) (h1 : 1048 ≤ k) (h2 : k < 1049) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1048 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1048_ok
theorem cr_1049_1050 (k : ℕ) (h1 : 1049 ≤ k) (h2 : k < 1050) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1049 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1049_ok
theorem cr_1048_1050 (k : ℕ) (h1 : 1048 ≤ k) (h2 : k < 1050) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1049 then cr_1048_1049 k h1 h else cr_1049_1050 k (by omega) h2
theorem cr_1047_1050 (k : ℕ) (h1 : 1047 ≤ k) (h2 : k < 1050) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1048 then cr_1047_1048 k h1 h else cr_1048_1050 k (by omega) h2
theorem cr_1045_1050 (k : ℕ) (h1 : 1045 ≤ k) (h2 : k < 1050) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1047 then cr_1045_1047 k h1 h else cr_1047_1050 k (by omega) h2
theorem cr_1050_1051 (k : ℕ) (h1 : 1050 ≤ k) (h2 : k < 1051) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1050 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1050_ok
theorem cr_1051_1052 (k : ℕ) (h1 : 1051 ≤ k) (h2 : k < 1052) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1051 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1051_ok
theorem cr_1050_1052 (k : ℕ) (h1 : 1050 ≤ k) (h2 : k < 1052) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1051 then cr_1050_1051 k h1 h else cr_1051_1052 k (by omega) h2
theorem cr_1052_1053 (k : ℕ) (h1 : 1052 ≤ k) (h2 : k < 1053) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1052 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1052_ok
theorem cr_1053_1054 (k : ℕ) (h1 : 1053 ≤ k) (h2 : k < 1054) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1053 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1053_ok
theorem cr_1054_1055 (k : ℕ) (h1 : 1054 ≤ k) (h2 : k < 1055) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1054 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1054_ok
theorem cr_1053_1055 (k : ℕ) (h1 : 1053 ≤ k) (h2 : k < 1055) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1054 then cr_1053_1054 k h1 h else cr_1054_1055 k (by omega) h2
theorem cr_1052_1055 (k : ℕ) (h1 : 1052 ≤ k) (h2 : k < 1055) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1053 then cr_1052_1053 k h1 h else cr_1053_1055 k (by omega) h2
theorem cr_1050_1055 (k : ℕ) (h1 : 1050 ≤ k) (h2 : k < 1055) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1052 then cr_1050_1052 k h1 h else cr_1052_1055 k (by omega) h2
theorem cr_1045_1055 (k : ℕ) (h1 : 1045 ≤ k) (h2 : k < 1055) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1050 then cr_1045_1050 k h1 h else cr_1050_1055 k (by omega) h2
theorem cr_1055_1056 (k : ℕ) (h1 : 1055 ≤ k) (h2 : k < 1056) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1055 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1055_ok
theorem cr_1056_1057 (k : ℕ) (h1 : 1056 ≤ k) (h2 : k < 1057) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1056 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1056_ok
theorem cr_1055_1057 (k : ℕ) (h1 : 1055 ≤ k) (h2 : k < 1057) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1056 then cr_1055_1056 k h1 h else cr_1056_1057 k (by omega) h2
theorem cr_1057_1058 (k : ℕ) (h1 : 1057 ≤ k) (h2 : k < 1058) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1057 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1057_ok
theorem cr_1058_1059 (k : ℕ) (h1 : 1058 ≤ k) (h2 : k < 1059) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1058 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1058_ok
theorem cr_1059_1060 (k : ℕ) (h1 : 1059 ≤ k) (h2 : k < 1060) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1059 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1059_ok
theorem cr_1058_1060 (k : ℕ) (h1 : 1058 ≤ k) (h2 : k < 1060) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1059 then cr_1058_1059 k h1 h else cr_1059_1060 k (by omega) h2
theorem cr_1057_1060 (k : ℕ) (h1 : 1057 ≤ k) (h2 : k < 1060) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1058 then cr_1057_1058 k h1 h else cr_1058_1060 k (by omega) h2
theorem cr_1055_1060 (k : ℕ) (h1 : 1055 ≤ k) (h2 : k < 1060) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1057 then cr_1055_1057 k h1 h else cr_1057_1060 k (by omega) h2
theorem cr_1060_1061 (k : ℕ) (h1 : 1060 ≤ k) (h2 : k < 1061) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1060 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1060_ok
theorem cr_1061_1062 (k : ℕ) (h1 : 1061 ≤ k) (h2 : k < 1062) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1061 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1061_ok
theorem cr_1062_1063 (k : ℕ) (h1 : 1062 ≤ k) (h2 : k < 1063) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1062 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1062_ok
theorem cr_1061_1063 (k : ℕ) (h1 : 1061 ≤ k) (h2 : k < 1063) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1062 then cr_1061_1062 k h1 h else cr_1062_1063 k (by omega) h2
theorem cr_1060_1063 (k : ℕ) (h1 : 1060 ≤ k) (h2 : k < 1063) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1061 then cr_1060_1061 k h1 h else cr_1061_1063 k (by omega) h2
theorem cr_1063_1064 (k : ℕ) (h1 : 1063 ≤ k) (h2 : k < 1064) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1063 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1063_ok
theorem cr_1064_1065 (k : ℕ) (h1 : 1064 ≤ k) (h2 : k < 1065) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1064 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1064_ok
theorem cr_1065_1066 (k : ℕ) (h1 : 1065 ≤ k) (h2 : k < 1066) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1065 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1065_ok
theorem cr_1064_1066 (k : ℕ) (h1 : 1064 ≤ k) (h2 : k < 1066) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1065 then cr_1064_1065 k h1 h else cr_1065_1066 k (by omega) h2
theorem cr_1063_1066 (k : ℕ) (h1 : 1063 ≤ k) (h2 : k < 1066) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1064 then cr_1063_1064 k h1 h else cr_1064_1066 k (by omega) h2
theorem cr_1060_1066 (k : ℕ) (h1 : 1060 ≤ k) (h2 : k < 1066) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1063 then cr_1060_1063 k h1 h else cr_1063_1066 k (by omega) h2
theorem cr_1055_1066 (k : ℕ) (h1 : 1055 ≤ k) (h2 : k < 1066) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1060 then cr_1055_1060 k h1 h else cr_1060_1066 k (by omega) h2
theorem cr_1045_1066 (k : ℕ) (h1 : 1045 ≤ k) (h2 : k < 1066) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1055 then cr_1045_1055 k h1 h else cr_1055_1066 k (by omega) h2
theorem cr_1025_1066 (k : ℕ) (h1 : 1025 ≤ k) (h2 : k < 1066) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1045 then cr_1025_1045 k h1 h else cr_1045_1066 k (by omega) h2
theorem cr_984_1066 (k : ℕ) (h1 : 984 ≤ k) (h2 : k < 1066) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1025 then cr_984_1025 k h1 h else cr_1025_1066 k (by omega) h2
theorem cr_1066_1067 (k : ℕ) (h1 : 1066 ≤ k) (h2 : k < 1067) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1066 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1066_ok
theorem cr_1067_1068 (k : ℕ) (h1 : 1067 ≤ k) (h2 : k < 1068) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1067 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1067_ok
theorem cr_1066_1068 (k : ℕ) (h1 : 1066 ≤ k) (h2 : k < 1068) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1067 then cr_1066_1067 k h1 h else cr_1067_1068 k (by omega) h2
theorem cr_1068_1069 (k : ℕ) (h1 : 1068 ≤ k) (h2 : k < 1069) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1068 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1068_ok
theorem cr_1069_1070 (k : ℕ) (h1 : 1069 ≤ k) (h2 : k < 1070) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1069 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1069_ok
theorem cr_1070_1071 (k : ℕ) (h1 : 1070 ≤ k) (h2 : k < 1071) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1070 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1070_ok
theorem cr_1069_1071 (k : ℕ) (h1 : 1069 ≤ k) (h2 : k < 1071) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1070 then cr_1069_1070 k h1 h else cr_1070_1071 k (by omega) h2
theorem cr_1068_1071 (k : ℕ) (h1 : 1068 ≤ k) (h2 : k < 1071) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1069 then cr_1068_1069 k h1 h else cr_1069_1071 k (by omega) h2
theorem cr_1066_1071 (k : ℕ) (h1 : 1066 ≤ k) (h2 : k < 1071) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1068 then cr_1066_1068 k h1 h else cr_1068_1071 k (by omega) h2
theorem cr_1071_1072 (k : ℕ) (h1 : 1071 ≤ k) (h2 : k < 1072) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1071 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1071_ok
theorem cr_1072_1073 (k : ℕ) (h1 : 1072 ≤ k) (h2 : k < 1073) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1072 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1072_ok
theorem cr_1071_1073 (k : ℕ) (h1 : 1071 ≤ k) (h2 : k < 1073) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1072 then cr_1071_1072 k h1 h else cr_1072_1073 k (by omega) h2
theorem cr_1073_1074 (k : ℕ) (h1 : 1073 ≤ k) (h2 : k < 1074) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1073 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1073_ok
theorem cr_1074_1075 (k : ℕ) (h1 : 1074 ≤ k) (h2 : k < 1075) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1074 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1074_ok
theorem cr_1075_1076 (k : ℕ) (h1 : 1075 ≤ k) (h2 : k < 1076) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1075 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1075_ok
theorem cr_1074_1076 (k : ℕ) (h1 : 1074 ≤ k) (h2 : k < 1076) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1075 then cr_1074_1075 k h1 h else cr_1075_1076 k (by omega) h2
theorem cr_1073_1076 (k : ℕ) (h1 : 1073 ≤ k) (h2 : k < 1076) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1074 then cr_1073_1074 k h1 h else cr_1074_1076 k (by omega) h2
theorem cr_1071_1076 (k : ℕ) (h1 : 1071 ≤ k) (h2 : k < 1076) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1073 then cr_1071_1073 k h1 h else cr_1073_1076 k (by omega) h2
theorem cr_1066_1076 (k : ℕ) (h1 : 1066 ≤ k) (h2 : k < 1076) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1071 then cr_1066_1071 k h1 h else cr_1071_1076 k (by omega) h2
theorem cr_1076_1077 (k : ℕ) (h1 : 1076 ≤ k) (h2 : k < 1077) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1076 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1076_ok
theorem cr_1077_1078 (k : ℕ) (h1 : 1077 ≤ k) (h2 : k < 1078) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1077 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1077_ok
theorem cr_1076_1078 (k : ℕ) (h1 : 1076 ≤ k) (h2 : k < 1078) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1077 then cr_1076_1077 k h1 h else cr_1077_1078 k (by omega) h2
theorem cr_1078_1079 (k : ℕ) (h1 : 1078 ≤ k) (h2 : k < 1079) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1078 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1078_ok
theorem cr_1079_1080 (k : ℕ) (h1 : 1079 ≤ k) (h2 : k < 1080) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1079 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1079_ok
theorem cr_1080_1081 (k : ℕ) (h1 : 1080 ≤ k) (h2 : k < 1081) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1080 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1080_ok
theorem cr_1079_1081 (k : ℕ) (h1 : 1079 ≤ k) (h2 : k < 1081) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1080 then cr_1079_1080 k h1 h else cr_1080_1081 k (by omega) h2
theorem cr_1078_1081 (k : ℕ) (h1 : 1078 ≤ k) (h2 : k < 1081) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1079 then cr_1078_1079 k h1 h else cr_1079_1081 k (by omega) h2
theorem cr_1076_1081 (k : ℕ) (h1 : 1076 ≤ k) (h2 : k < 1081) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1078 then cr_1076_1078 k h1 h else cr_1078_1081 k (by omega) h2
theorem cr_1081_1082 (k : ℕ) (h1 : 1081 ≤ k) (h2 : k < 1082) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1081 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1081_ok
theorem cr_1082_1083 (k : ℕ) (h1 : 1082 ≤ k) (h2 : k < 1083) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1082 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1082_ok
theorem cr_1081_1083 (k : ℕ) (h1 : 1081 ≤ k) (h2 : k < 1083) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1082 then cr_1081_1082 k h1 h else cr_1082_1083 k (by omega) h2
theorem cr_1083_1084 (k : ℕ) (h1 : 1083 ≤ k) (h2 : k < 1084) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1083 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1083_ok
theorem cr_1084_1085 (k : ℕ) (h1 : 1084 ≤ k) (h2 : k < 1085) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1084 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1084_ok
theorem cr_1085_1086 (k : ℕ) (h1 : 1085 ≤ k) (h2 : k < 1086) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1085 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1085_ok
theorem cr_1084_1086 (k : ℕ) (h1 : 1084 ≤ k) (h2 : k < 1086) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1085 then cr_1084_1085 k h1 h else cr_1085_1086 k (by omega) h2
theorem cr_1083_1086 (k : ℕ) (h1 : 1083 ≤ k) (h2 : k < 1086) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1084 then cr_1083_1084 k h1 h else cr_1084_1086 k (by omega) h2
theorem cr_1081_1086 (k : ℕ) (h1 : 1081 ≤ k) (h2 : k < 1086) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1083 then cr_1081_1083 k h1 h else cr_1083_1086 k (by omega) h2
theorem cr_1076_1086 (k : ℕ) (h1 : 1076 ≤ k) (h2 : k < 1086) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1081 then cr_1076_1081 k h1 h else cr_1081_1086 k (by omega) h2
theorem cr_1066_1086 (k : ℕ) (h1 : 1066 ≤ k) (h2 : k < 1086) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1076 then cr_1066_1076 k h1 h else cr_1076_1086 k (by omega) h2
theorem cr_1086_1087 (k : ℕ) (h1 : 1086 ≤ k) (h2 : k < 1087) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1086 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1086_ok
theorem cr_1087_1088 (k : ℕ) (h1 : 1087 ≤ k) (h2 : k < 1088) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1087 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1087_ok
theorem cr_1086_1088 (k : ℕ) (h1 : 1086 ≤ k) (h2 : k < 1088) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1087 then cr_1086_1087 k h1 h else cr_1087_1088 k (by omega) h2
theorem cr_1088_1089 (k : ℕ) (h1 : 1088 ≤ k) (h2 : k < 1089) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1088 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1088_ok
theorem cr_1089_1090 (k : ℕ) (h1 : 1089 ≤ k) (h2 : k < 1090) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1089 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1089_ok
theorem cr_1090_1091 (k : ℕ) (h1 : 1090 ≤ k) (h2 : k < 1091) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1090 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1090_ok
theorem cr_1089_1091 (k : ℕ) (h1 : 1089 ≤ k) (h2 : k < 1091) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1090 then cr_1089_1090 k h1 h else cr_1090_1091 k (by omega) h2
theorem cr_1088_1091 (k : ℕ) (h1 : 1088 ≤ k) (h2 : k < 1091) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1089 then cr_1088_1089 k h1 h else cr_1089_1091 k (by omega) h2
theorem cr_1086_1091 (k : ℕ) (h1 : 1086 ≤ k) (h2 : k < 1091) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1088 then cr_1086_1088 k h1 h else cr_1088_1091 k (by omega) h2
theorem cr_1091_1092 (k : ℕ) (h1 : 1091 ≤ k) (h2 : k < 1092) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1091 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1091_ok
theorem cr_1092_1093 (k : ℕ) (h1 : 1092 ≤ k) (h2 : k < 1093) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1092 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1092_ok
theorem cr_1091_1093 (k : ℕ) (h1 : 1091 ≤ k) (h2 : k < 1093) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1092 then cr_1091_1092 k h1 h else cr_1092_1093 k (by omega) h2
theorem cr_1093_1094 (k : ℕ) (h1 : 1093 ≤ k) (h2 : k < 1094) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1093 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1093_ok
theorem cr_1094_1095 (k : ℕ) (h1 : 1094 ≤ k) (h2 : k < 1095) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1094 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1094_ok
theorem cr_1095_1096 (k : ℕ) (h1 : 1095 ≤ k) (h2 : k < 1096) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1095 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1095_ok
theorem cr_1094_1096 (k : ℕ) (h1 : 1094 ≤ k) (h2 : k < 1096) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1095 then cr_1094_1095 k h1 h else cr_1095_1096 k (by omega) h2
theorem cr_1093_1096 (k : ℕ) (h1 : 1093 ≤ k) (h2 : k < 1096) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1094 then cr_1093_1094 k h1 h else cr_1094_1096 k (by omega) h2
theorem cr_1091_1096 (k : ℕ) (h1 : 1091 ≤ k) (h2 : k < 1096) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1093 then cr_1091_1093 k h1 h else cr_1093_1096 k (by omega) h2
theorem cr_1086_1096 (k : ℕ) (h1 : 1086 ≤ k) (h2 : k < 1096) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1091 then cr_1086_1091 k h1 h else cr_1091_1096 k (by omega) h2
theorem cr_1096_1097 (k : ℕ) (h1 : 1096 ≤ k) (h2 : k < 1097) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1096 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1096_ok
theorem cr_1097_1098 (k : ℕ) (h1 : 1097 ≤ k) (h2 : k < 1098) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1097 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1097_ok
theorem cr_1096_1098 (k : ℕ) (h1 : 1096 ≤ k) (h2 : k < 1098) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1097 then cr_1096_1097 k h1 h else cr_1097_1098 k (by omega) h2
theorem cr_1098_1099 (k : ℕ) (h1 : 1098 ≤ k) (h2 : k < 1099) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1098 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1098_ok
theorem cr_1099_1100 (k : ℕ) (h1 : 1099 ≤ k) (h2 : k < 1100) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1099 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1099_ok
theorem cr_1100_1101 (k : ℕ) (h1 : 1100 ≤ k) (h2 : k < 1101) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1100 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1100_ok
theorem cr_1099_1101 (k : ℕ) (h1 : 1099 ≤ k) (h2 : k < 1101) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1100 then cr_1099_1100 k h1 h else cr_1100_1101 k (by omega) h2
theorem cr_1098_1101 (k : ℕ) (h1 : 1098 ≤ k) (h2 : k < 1101) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1099 then cr_1098_1099 k h1 h else cr_1099_1101 k (by omega) h2
theorem cr_1096_1101 (k : ℕ) (h1 : 1096 ≤ k) (h2 : k < 1101) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1098 then cr_1096_1098 k h1 h else cr_1098_1101 k (by omega) h2
theorem cr_1101_1102 (k : ℕ) (h1 : 1101 ≤ k) (h2 : k < 1102) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1101 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1101_ok
theorem cr_1102_1103 (k : ℕ) (h1 : 1102 ≤ k) (h2 : k < 1103) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1102 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1102_ok
theorem cr_1103_1104 (k : ℕ) (h1 : 1103 ≤ k) (h2 : k < 1104) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1103 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1103_ok
theorem cr_1102_1104 (k : ℕ) (h1 : 1102 ≤ k) (h2 : k < 1104) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1103 then cr_1102_1103 k h1 h else cr_1103_1104 k (by omega) h2
theorem cr_1101_1104 (k : ℕ) (h1 : 1101 ≤ k) (h2 : k < 1104) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1102 then cr_1101_1102 k h1 h else cr_1102_1104 k (by omega) h2
theorem cr_1104_1105 (k : ℕ) (h1 : 1104 ≤ k) (h2 : k < 1105) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1104 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1104_ok
theorem cr_1105_1106 (k : ℕ) (h1 : 1105 ≤ k) (h2 : k < 1106) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1105 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1105_ok
theorem cr_1106_1107 (k : ℕ) (h1 : 1106 ≤ k) (h2 : k < 1107) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1106 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1106_ok
theorem cr_1105_1107 (k : ℕ) (h1 : 1105 ≤ k) (h2 : k < 1107) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1106 then cr_1105_1106 k h1 h else cr_1106_1107 k (by omega) h2
theorem cr_1104_1107 (k : ℕ) (h1 : 1104 ≤ k) (h2 : k < 1107) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1105 then cr_1104_1105 k h1 h else cr_1105_1107 k (by omega) h2
theorem cr_1101_1107 (k : ℕ) (h1 : 1101 ≤ k) (h2 : k < 1107) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1104 then cr_1101_1104 k h1 h else cr_1104_1107 k (by omega) h2
theorem cr_1096_1107 (k : ℕ) (h1 : 1096 ≤ k) (h2 : k < 1107) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1101 then cr_1096_1101 k h1 h else cr_1101_1107 k (by omega) h2
theorem cr_1086_1107 (k : ℕ) (h1 : 1086 ≤ k) (h2 : k < 1107) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1096 then cr_1086_1096 k h1 h else cr_1096_1107 k (by omega) h2
theorem cr_1066_1107 (k : ℕ) (h1 : 1066 ≤ k) (h2 : k < 1107) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1086 then cr_1066_1086 k h1 h else cr_1086_1107 k (by omega) h2
theorem cr_1107_1108 (k : ℕ) (h1 : 1107 ≤ k) (h2 : k < 1108) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1107 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1107_ok
theorem cr_1108_1109 (k : ℕ) (h1 : 1108 ≤ k) (h2 : k < 1109) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1108 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1108_ok
theorem cr_1107_1109 (k : ℕ) (h1 : 1107 ≤ k) (h2 : k < 1109) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1108 then cr_1107_1108 k h1 h else cr_1108_1109 k (by omega) h2
theorem cr_1109_1110 (k : ℕ) (h1 : 1109 ≤ k) (h2 : k < 1110) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1109 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1109_ok
theorem cr_1110_1111 (k : ℕ) (h1 : 1110 ≤ k) (h2 : k < 1111) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1110 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1110_ok
theorem cr_1111_1112 (k : ℕ) (h1 : 1111 ≤ k) (h2 : k < 1112) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1111 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1111_ok
theorem cr_1110_1112 (k : ℕ) (h1 : 1110 ≤ k) (h2 : k < 1112) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1111 then cr_1110_1111 k h1 h else cr_1111_1112 k (by omega) h2
theorem cr_1109_1112 (k : ℕ) (h1 : 1109 ≤ k) (h2 : k < 1112) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1110 then cr_1109_1110 k h1 h else cr_1110_1112 k (by omega) h2
theorem cr_1107_1112 (k : ℕ) (h1 : 1107 ≤ k) (h2 : k < 1112) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1109 then cr_1107_1109 k h1 h else cr_1109_1112 k (by omega) h2
theorem cr_1112_1113 (k : ℕ) (h1 : 1112 ≤ k) (h2 : k < 1113) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1112 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1112_ok
theorem cr_1113_1114 (k : ℕ) (h1 : 1113 ≤ k) (h2 : k < 1114) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1113 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1113_ok
theorem cr_1112_1114 (k : ℕ) (h1 : 1112 ≤ k) (h2 : k < 1114) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1113 then cr_1112_1113 k h1 h else cr_1113_1114 k (by omega) h2
theorem cr_1114_1115 (k : ℕ) (h1 : 1114 ≤ k) (h2 : k < 1115) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1114 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1114_ok
theorem cr_1115_1116 (k : ℕ) (h1 : 1115 ≤ k) (h2 : k < 1116) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1115 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1115_ok
theorem cr_1116_1117 (k : ℕ) (h1 : 1116 ≤ k) (h2 : k < 1117) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1116 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1116_ok
theorem cr_1115_1117 (k : ℕ) (h1 : 1115 ≤ k) (h2 : k < 1117) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1116 then cr_1115_1116 k h1 h else cr_1116_1117 k (by omega) h2
theorem cr_1114_1117 (k : ℕ) (h1 : 1114 ≤ k) (h2 : k < 1117) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1115 then cr_1114_1115 k h1 h else cr_1115_1117 k (by omega) h2
theorem cr_1112_1117 (k : ℕ) (h1 : 1112 ≤ k) (h2 : k < 1117) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1114 then cr_1112_1114 k h1 h else cr_1114_1117 k (by omega) h2
theorem cr_1107_1117 (k : ℕ) (h1 : 1107 ≤ k) (h2 : k < 1117) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1112 then cr_1107_1112 k h1 h else cr_1112_1117 k (by omega) h2
theorem cr_1117_1118 (k : ℕ) (h1 : 1117 ≤ k) (h2 : k < 1118) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1117 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1117_ok
theorem cr_1118_1119 (k : ℕ) (h1 : 1118 ≤ k) (h2 : k < 1119) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1118 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1118_ok
theorem cr_1117_1119 (k : ℕ) (h1 : 1117 ≤ k) (h2 : k < 1119) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1118 then cr_1117_1118 k h1 h else cr_1118_1119 k (by omega) h2
theorem cr_1119_1120 (k : ℕ) (h1 : 1119 ≤ k) (h2 : k < 1120) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1119 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1119_ok
theorem cr_1120_1121 (k : ℕ) (h1 : 1120 ≤ k) (h2 : k < 1121) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1120 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1120_ok
theorem cr_1121_1122 (k : ℕ) (h1 : 1121 ≤ k) (h2 : k < 1122) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1121 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1121_ok
theorem cr_1120_1122 (k : ℕ) (h1 : 1120 ≤ k) (h2 : k < 1122) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1121 then cr_1120_1121 k h1 h else cr_1121_1122 k (by omega) h2
theorem cr_1119_1122 (k : ℕ) (h1 : 1119 ≤ k) (h2 : k < 1122) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1120 then cr_1119_1120 k h1 h else cr_1120_1122 k (by omega) h2
theorem cr_1117_1122 (k : ℕ) (h1 : 1117 ≤ k) (h2 : k < 1122) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1119 then cr_1117_1119 k h1 h else cr_1119_1122 k (by omega) h2
theorem cr_1122_1123 (k : ℕ) (h1 : 1122 ≤ k) (h2 : k < 1123) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1122 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1122_ok
theorem cr_1123_1124 (k : ℕ) (h1 : 1123 ≤ k) (h2 : k < 1124) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1123 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1123_ok
theorem cr_1122_1124 (k : ℕ) (h1 : 1122 ≤ k) (h2 : k < 1124) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1123 then cr_1122_1123 k h1 h else cr_1123_1124 k (by omega) h2
theorem cr_1124_1125 (k : ℕ) (h1 : 1124 ≤ k) (h2 : k < 1125) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1124 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1124_ok
theorem cr_1125_1126 (k : ℕ) (h1 : 1125 ≤ k) (h2 : k < 1126) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1125 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1125_ok
theorem cr_1126_1127 (k : ℕ) (h1 : 1126 ≤ k) (h2 : k < 1127) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1126 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1126_ok
theorem cr_1125_1127 (k : ℕ) (h1 : 1125 ≤ k) (h2 : k < 1127) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1126 then cr_1125_1126 k h1 h else cr_1126_1127 k (by omega) h2
theorem cr_1124_1127 (k : ℕ) (h1 : 1124 ≤ k) (h2 : k < 1127) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1125 then cr_1124_1125 k h1 h else cr_1125_1127 k (by omega) h2
theorem cr_1122_1127 (k : ℕ) (h1 : 1122 ≤ k) (h2 : k < 1127) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1124 then cr_1122_1124 k h1 h else cr_1124_1127 k (by omega) h2
theorem cr_1117_1127 (k : ℕ) (h1 : 1117 ≤ k) (h2 : k < 1127) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1122 then cr_1117_1122 k h1 h else cr_1122_1127 k (by omega) h2
theorem cr_1107_1127 (k : ℕ) (h1 : 1107 ≤ k) (h2 : k < 1127) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1117 then cr_1107_1117 k h1 h else cr_1117_1127 k (by omega) h2
theorem cr_1127_1128 (k : ℕ) (h1 : 1127 ≤ k) (h2 : k < 1128) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1127 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1127_ok
theorem cr_1128_1129 (k : ℕ) (h1 : 1128 ≤ k) (h2 : k < 1129) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1128 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1128_ok
theorem cr_1127_1129 (k : ℕ) (h1 : 1127 ≤ k) (h2 : k < 1129) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1128 then cr_1127_1128 k h1 h else cr_1128_1129 k (by omega) h2
theorem cr_1129_1130 (k : ℕ) (h1 : 1129 ≤ k) (h2 : k < 1130) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1129 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1129_ok
theorem cr_1130_1131 (k : ℕ) (h1 : 1130 ≤ k) (h2 : k < 1131) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1130 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1130_ok
theorem cr_1131_1132 (k : ℕ) (h1 : 1131 ≤ k) (h2 : k < 1132) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1131 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1131_ok
theorem cr_1130_1132 (k : ℕ) (h1 : 1130 ≤ k) (h2 : k < 1132) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1131 then cr_1130_1131 k h1 h else cr_1131_1132 k (by omega) h2
theorem cr_1129_1132 (k : ℕ) (h1 : 1129 ≤ k) (h2 : k < 1132) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1130 then cr_1129_1130 k h1 h else cr_1130_1132 k (by omega) h2
theorem cr_1127_1132 (k : ℕ) (h1 : 1127 ≤ k) (h2 : k < 1132) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1129 then cr_1127_1129 k h1 h else cr_1129_1132 k (by omega) h2
theorem cr_1132_1133 (k : ℕ) (h1 : 1132 ≤ k) (h2 : k < 1133) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1132 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1132_ok
theorem cr_1133_1134 (k : ℕ) (h1 : 1133 ≤ k) (h2 : k < 1134) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1133 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1133_ok
theorem cr_1132_1134 (k : ℕ) (h1 : 1132 ≤ k) (h2 : k < 1134) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1133 then cr_1132_1133 k h1 h else cr_1133_1134 k (by omega) h2
theorem cr_1134_1135 (k : ℕ) (h1 : 1134 ≤ k) (h2 : k < 1135) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1134 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1134_ok
theorem cr_1135_1136 (k : ℕ) (h1 : 1135 ≤ k) (h2 : k < 1136) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1135 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1135_ok
theorem cr_1136_1137 (k : ℕ) (h1 : 1136 ≤ k) (h2 : k < 1137) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1136 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1136_ok
theorem cr_1135_1137 (k : ℕ) (h1 : 1135 ≤ k) (h2 : k < 1137) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1136 then cr_1135_1136 k h1 h else cr_1136_1137 k (by omega) h2
theorem cr_1134_1137 (k : ℕ) (h1 : 1134 ≤ k) (h2 : k < 1137) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1135 then cr_1134_1135 k h1 h else cr_1135_1137 k (by omega) h2
theorem cr_1132_1137 (k : ℕ) (h1 : 1132 ≤ k) (h2 : k < 1137) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1134 then cr_1132_1134 k h1 h else cr_1134_1137 k (by omega) h2
theorem cr_1127_1137 (k : ℕ) (h1 : 1127 ≤ k) (h2 : k < 1137) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1132 then cr_1127_1132 k h1 h else cr_1132_1137 k (by omega) h2
theorem cr_1137_1138 (k : ℕ) (h1 : 1137 ≤ k) (h2 : k < 1138) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1137 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1137_ok
theorem cr_1138_1139 (k : ℕ) (h1 : 1138 ≤ k) (h2 : k < 1139) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1138 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1138_ok
theorem cr_1137_1139 (k : ℕ) (h1 : 1137 ≤ k) (h2 : k < 1139) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1138 then cr_1137_1138 k h1 h else cr_1138_1139 k (by omega) h2
theorem cr_1139_1140 (k : ℕ) (h1 : 1139 ≤ k) (h2 : k < 1140) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1139 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1139_ok
theorem cr_1140_1141 (k : ℕ) (h1 : 1140 ≤ k) (h2 : k < 1141) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1140 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1140_ok
theorem cr_1141_1142 (k : ℕ) (h1 : 1141 ≤ k) (h2 : k < 1142) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1141 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1141_ok
theorem cr_1140_1142 (k : ℕ) (h1 : 1140 ≤ k) (h2 : k < 1142) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1141 then cr_1140_1141 k h1 h else cr_1141_1142 k (by omega) h2
theorem cr_1139_1142 (k : ℕ) (h1 : 1139 ≤ k) (h2 : k < 1142) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1140 then cr_1139_1140 k h1 h else cr_1140_1142 k (by omega) h2
theorem cr_1137_1142 (k : ℕ) (h1 : 1137 ≤ k) (h2 : k < 1142) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1139 then cr_1137_1139 k h1 h else cr_1139_1142 k (by omega) h2
theorem cr_1142_1143 (k : ℕ) (h1 : 1142 ≤ k) (h2 : k < 1143) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1142 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1142_ok
theorem cr_1143_1144 (k : ℕ) (h1 : 1143 ≤ k) (h2 : k < 1144) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1143 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1143_ok
theorem cr_1144_1145 (k : ℕ) (h1 : 1144 ≤ k) (h2 : k < 1145) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1144 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1144_ok
theorem cr_1143_1145 (k : ℕ) (h1 : 1143 ≤ k) (h2 : k < 1145) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1144 then cr_1143_1144 k h1 h else cr_1144_1145 k (by omega) h2
theorem cr_1142_1145 (k : ℕ) (h1 : 1142 ≤ k) (h2 : k < 1145) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1143 then cr_1142_1143 k h1 h else cr_1143_1145 k (by omega) h2
theorem cr_1145_1146 (k : ℕ) (h1 : 1145 ≤ k) (h2 : k < 1146) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1145 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1145_ok
theorem cr_1146_1147 (k : ℕ) (h1 : 1146 ≤ k) (h2 : k < 1147) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1146 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1146_ok
theorem cr_1147_1148 (k : ℕ) (h1 : 1147 ≤ k) (h2 : k < 1148) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1147 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1147_ok
theorem cr_1146_1148 (k : ℕ) (h1 : 1146 ≤ k) (h2 : k < 1148) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1147 then cr_1146_1147 k h1 h else cr_1147_1148 k (by omega) h2
theorem cr_1145_1148 (k : ℕ) (h1 : 1145 ≤ k) (h2 : k < 1148) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1146 then cr_1145_1146 k h1 h else cr_1146_1148 k (by omega) h2
theorem cr_1142_1148 (k : ℕ) (h1 : 1142 ≤ k) (h2 : k < 1148) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1145 then cr_1142_1145 k h1 h else cr_1145_1148 k (by omega) h2
theorem cr_1137_1148 (k : ℕ) (h1 : 1137 ≤ k) (h2 : k < 1148) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1142 then cr_1137_1142 k h1 h else cr_1142_1148 k (by omega) h2
theorem cr_1127_1148 (k : ℕ) (h1 : 1127 ≤ k) (h2 : k < 1148) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1137 then cr_1127_1137 k h1 h else cr_1137_1148 k (by omega) h2
theorem cr_1107_1148 (k : ℕ) (h1 : 1107 ≤ k) (h2 : k < 1148) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1127 then cr_1107_1127 k h1 h else cr_1127_1148 k (by omega) h2
theorem cr_1066_1148 (k : ℕ) (h1 : 1066 ≤ k) (h2 : k < 1148) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1107 then cr_1066_1107 k h1 h else cr_1107_1148 k (by omega) h2
theorem cr_984_1148 (k : ℕ) (h1 : 984 ≤ k) (h2 : k < 1148) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1066 then cr_984_1066 k h1 h else cr_1066_1148 k (by omega) h2
theorem cr_1148_1149 (k : ℕ) (h1 : 1148 ≤ k) (h2 : k < 1149) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1148 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1148_ok
theorem cr_1149_1150 (k : ℕ) (h1 : 1149 ≤ k) (h2 : k < 1150) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1149 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1149_ok
theorem cr_1148_1150 (k : ℕ) (h1 : 1148 ≤ k) (h2 : k < 1150) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1149 then cr_1148_1149 k h1 h else cr_1149_1150 k (by omega) h2
theorem cr_1150_1151 (k : ℕ) (h1 : 1150 ≤ k) (h2 : k < 1151) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1150 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1150_ok
theorem cr_1151_1152 (k : ℕ) (h1 : 1151 ≤ k) (h2 : k < 1152) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1151 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1151_ok
theorem cr_1152_1153 (k : ℕ) (h1 : 1152 ≤ k) (h2 : k < 1153) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1152 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1152_ok
theorem cr_1151_1153 (k : ℕ) (h1 : 1151 ≤ k) (h2 : k < 1153) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1152 then cr_1151_1152 k h1 h else cr_1152_1153 k (by omega) h2
theorem cr_1150_1153 (k : ℕ) (h1 : 1150 ≤ k) (h2 : k < 1153) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1151 then cr_1150_1151 k h1 h else cr_1151_1153 k (by omega) h2
theorem cr_1148_1153 (k : ℕ) (h1 : 1148 ≤ k) (h2 : k < 1153) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1150 then cr_1148_1150 k h1 h else cr_1150_1153 k (by omega) h2
theorem cr_1153_1154 (k : ℕ) (h1 : 1153 ≤ k) (h2 : k < 1154) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1153 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1153_ok
theorem cr_1154_1155 (k : ℕ) (h1 : 1154 ≤ k) (h2 : k < 1155) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1154 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1154_ok
theorem cr_1153_1155 (k : ℕ) (h1 : 1153 ≤ k) (h2 : k < 1155) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1154 then cr_1153_1154 k h1 h else cr_1154_1155 k (by omega) h2
theorem cr_1155_1156 (k : ℕ) (h1 : 1155 ≤ k) (h2 : k < 1156) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1155 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1155_ok
theorem cr_1156_1157 (k : ℕ) (h1 : 1156 ≤ k) (h2 : k < 1157) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1156 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1156_ok
theorem cr_1157_1158 (k : ℕ) (h1 : 1157 ≤ k) (h2 : k < 1158) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1157 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1157_ok
theorem cr_1156_1158 (k : ℕ) (h1 : 1156 ≤ k) (h2 : k < 1158) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1157 then cr_1156_1157 k h1 h else cr_1157_1158 k (by omega) h2
theorem cr_1155_1158 (k : ℕ) (h1 : 1155 ≤ k) (h2 : k < 1158) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1156 then cr_1155_1156 k h1 h else cr_1156_1158 k (by omega) h2
theorem cr_1153_1158 (k : ℕ) (h1 : 1153 ≤ k) (h2 : k < 1158) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1155 then cr_1153_1155 k h1 h else cr_1155_1158 k (by omega) h2
theorem cr_1148_1158 (k : ℕ) (h1 : 1148 ≤ k) (h2 : k < 1158) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1153 then cr_1148_1153 k h1 h else cr_1153_1158 k (by omega) h2
theorem cr_1158_1159 (k : ℕ) (h1 : 1158 ≤ k) (h2 : k < 1159) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1158 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1158_ok
theorem cr_1159_1160 (k : ℕ) (h1 : 1159 ≤ k) (h2 : k < 1160) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1159 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1159_ok
theorem cr_1158_1160 (k : ℕ) (h1 : 1158 ≤ k) (h2 : k < 1160) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1159 then cr_1158_1159 k h1 h else cr_1159_1160 k (by omega) h2
theorem cr_1160_1161 (k : ℕ) (h1 : 1160 ≤ k) (h2 : k < 1161) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1160 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1160_ok
theorem cr_1161_1162 (k : ℕ) (h1 : 1161 ≤ k) (h2 : k < 1162) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1161 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1161_ok
theorem cr_1162_1163 (k : ℕ) (h1 : 1162 ≤ k) (h2 : k < 1163) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1162 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1162_ok
theorem cr_1161_1163 (k : ℕ) (h1 : 1161 ≤ k) (h2 : k < 1163) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1162 then cr_1161_1162 k h1 h else cr_1162_1163 k (by omega) h2
theorem cr_1160_1163 (k : ℕ) (h1 : 1160 ≤ k) (h2 : k < 1163) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1161 then cr_1160_1161 k h1 h else cr_1161_1163 k (by omega) h2
theorem cr_1158_1163 (k : ℕ) (h1 : 1158 ≤ k) (h2 : k < 1163) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1160 then cr_1158_1160 k h1 h else cr_1160_1163 k (by omega) h2
theorem cr_1163_1164 (k : ℕ) (h1 : 1163 ≤ k) (h2 : k < 1164) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1163 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1163_ok
theorem cr_1164_1165 (k : ℕ) (h1 : 1164 ≤ k) (h2 : k < 1165) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1164 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1164_ok
theorem cr_1163_1165 (k : ℕ) (h1 : 1163 ≤ k) (h2 : k < 1165) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1164 then cr_1163_1164 k h1 h else cr_1164_1165 k (by omega) h2
theorem cr_1165_1166 (k : ℕ) (h1 : 1165 ≤ k) (h2 : k < 1166) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1165 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1165_ok
theorem cr_1166_1167 (k : ℕ) (h1 : 1166 ≤ k) (h2 : k < 1167) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1166 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1166_ok
theorem cr_1167_1168 (k : ℕ) (h1 : 1167 ≤ k) (h2 : k < 1168) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1167 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1167_ok
theorem cr_1166_1168 (k : ℕ) (h1 : 1166 ≤ k) (h2 : k < 1168) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1167 then cr_1166_1167 k h1 h else cr_1167_1168 k (by omega) h2
theorem cr_1165_1168 (k : ℕ) (h1 : 1165 ≤ k) (h2 : k < 1168) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1166 then cr_1165_1166 k h1 h else cr_1166_1168 k (by omega) h2
theorem cr_1163_1168 (k : ℕ) (h1 : 1163 ≤ k) (h2 : k < 1168) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1165 then cr_1163_1165 k h1 h else cr_1165_1168 k (by omega) h2
theorem cr_1158_1168 (k : ℕ) (h1 : 1158 ≤ k) (h2 : k < 1168) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1163 then cr_1158_1163 k h1 h else cr_1163_1168 k (by omega) h2
theorem cr_1148_1168 (k : ℕ) (h1 : 1148 ≤ k) (h2 : k < 1168) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1158 then cr_1148_1158 k h1 h else cr_1158_1168 k (by omega) h2
theorem cr_1168_1169 (k : ℕ) (h1 : 1168 ≤ k) (h2 : k < 1169) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1168 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1168_ok
theorem cr_1169_1170 (k : ℕ) (h1 : 1169 ≤ k) (h2 : k < 1170) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1169 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1169_ok
theorem cr_1168_1170 (k : ℕ) (h1 : 1168 ≤ k) (h2 : k < 1170) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1169 then cr_1168_1169 k h1 h else cr_1169_1170 k (by omega) h2
theorem cr_1170_1171 (k : ℕ) (h1 : 1170 ≤ k) (h2 : k < 1171) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1170 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1170_ok
theorem cr_1171_1172 (k : ℕ) (h1 : 1171 ≤ k) (h2 : k < 1172) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1171 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1171_ok
theorem cr_1172_1173 (k : ℕ) (h1 : 1172 ≤ k) (h2 : k < 1173) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1172 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1172_ok
theorem cr_1171_1173 (k : ℕ) (h1 : 1171 ≤ k) (h2 : k < 1173) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1172 then cr_1171_1172 k h1 h else cr_1172_1173 k (by omega) h2
theorem cr_1170_1173 (k : ℕ) (h1 : 1170 ≤ k) (h2 : k < 1173) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1171 then cr_1170_1171 k h1 h else cr_1171_1173 k (by omega) h2
theorem cr_1168_1173 (k : ℕ) (h1 : 1168 ≤ k) (h2 : k < 1173) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1170 then cr_1168_1170 k h1 h else cr_1170_1173 k (by omega) h2
theorem cr_1173_1174 (k : ℕ) (h1 : 1173 ≤ k) (h2 : k < 1174) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1173 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1173_ok
theorem cr_1174_1175 (k : ℕ) (h1 : 1174 ≤ k) (h2 : k < 1175) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1174 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1174_ok
theorem cr_1173_1175 (k : ℕ) (h1 : 1173 ≤ k) (h2 : k < 1175) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1174 then cr_1173_1174 k h1 h else cr_1174_1175 k (by omega) h2
theorem cr_1175_1176 (k : ℕ) (h1 : 1175 ≤ k) (h2 : k < 1176) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1175 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1175_ok
theorem cr_1176_1177 (k : ℕ) (h1 : 1176 ≤ k) (h2 : k < 1177) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1176 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1176_ok
theorem cr_1177_1178 (k : ℕ) (h1 : 1177 ≤ k) (h2 : k < 1178) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1177 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1177_ok
theorem cr_1176_1178 (k : ℕ) (h1 : 1176 ≤ k) (h2 : k < 1178) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1177 then cr_1176_1177 k h1 h else cr_1177_1178 k (by omega) h2
theorem cr_1175_1178 (k : ℕ) (h1 : 1175 ≤ k) (h2 : k < 1178) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1176 then cr_1175_1176 k h1 h else cr_1176_1178 k (by omega) h2
theorem cr_1173_1178 (k : ℕ) (h1 : 1173 ≤ k) (h2 : k < 1178) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1175 then cr_1173_1175 k h1 h else cr_1175_1178 k (by omega) h2
theorem cr_1168_1178 (k : ℕ) (h1 : 1168 ≤ k) (h2 : k < 1178) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1173 then cr_1168_1173 k h1 h else cr_1173_1178 k (by omega) h2
theorem cr_1178_1179 (k : ℕ) (h1 : 1178 ≤ k) (h2 : k < 1179) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1178 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1178_ok
theorem cr_1179_1180 (k : ℕ) (h1 : 1179 ≤ k) (h2 : k < 1180) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1179 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1179_ok
theorem cr_1178_1180 (k : ℕ) (h1 : 1178 ≤ k) (h2 : k < 1180) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1179 then cr_1178_1179 k h1 h else cr_1179_1180 k (by omega) h2
theorem cr_1180_1181 (k : ℕ) (h1 : 1180 ≤ k) (h2 : k < 1181) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1180 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1180_ok
theorem cr_1181_1182 (k : ℕ) (h1 : 1181 ≤ k) (h2 : k < 1182) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1181 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1181_ok
theorem cr_1182_1183 (k : ℕ) (h1 : 1182 ≤ k) (h2 : k < 1183) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1182 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1182_ok
theorem cr_1181_1183 (k : ℕ) (h1 : 1181 ≤ k) (h2 : k < 1183) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1182 then cr_1181_1182 k h1 h else cr_1182_1183 k (by omega) h2
theorem cr_1180_1183 (k : ℕ) (h1 : 1180 ≤ k) (h2 : k < 1183) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1181 then cr_1180_1181 k h1 h else cr_1181_1183 k (by omega) h2
theorem cr_1178_1183 (k : ℕ) (h1 : 1178 ≤ k) (h2 : k < 1183) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1180 then cr_1178_1180 k h1 h else cr_1180_1183 k (by omega) h2
theorem cr_1183_1184 (k : ℕ) (h1 : 1183 ≤ k) (h2 : k < 1184) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1183 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1183_ok
theorem cr_1184_1185 (k : ℕ) (h1 : 1184 ≤ k) (h2 : k < 1185) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1184 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1184_ok
theorem cr_1185_1186 (k : ℕ) (h1 : 1185 ≤ k) (h2 : k < 1186) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1185 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1185_ok
theorem cr_1184_1186 (k : ℕ) (h1 : 1184 ≤ k) (h2 : k < 1186) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1185 then cr_1184_1185 k h1 h else cr_1185_1186 k (by omega) h2
theorem cr_1183_1186 (k : ℕ) (h1 : 1183 ≤ k) (h2 : k < 1186) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1184 then cr_1183_1184 k h1 h else cr_1184_1186 k (by omega) h2
theorem cr_1186_1187 (k : ℕ) (h1 : 1186 ≤ k) (h2 : k < 1187) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1186 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1186_ok
theorem cr_1187_1188 (k : ℕ) (h1 : 1187 ≤ k) (h2 : k < 1188) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1187 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1187_ok
theorem cr_1188_1189 (k : ℕ) (h1 : 1188 ≤ k) (h2 : k < 1189) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1188 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1188_ok
theorem cr_1187_1189 (k : ℕ) (h1 : 1187 ≤ k) (h2 : k < 1189) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1188 then cr_1187_1188 k h1 h else cr_1188_1189 k (by omega) h2
theorem cr_1186_1189 (k : ℕ) (h1 : 1186 ≤ k) (h2 : k < 1189) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1187 then cr_1186_1187 k h1 h else cr_1187_1189 k (by omega) h2
theorem cr_1183_1189 (k : ℕ) (h1 : 1183 ≤ k) (h2 : k < 1189) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1186 then cr_1183_1186 k h1 h else cr_1186_1189 k (by omega) h2
theorem cr_1178_1189 (k : ℕ) (h1 : 1178 ≤ k) (h2 : k < 1189) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1183 then cr_1178_1183 k h1 h else cr_1183_1189 k (by omega) h2
theorem cr_1168_1189 (k : ℕ) (h1 : 1168 ≤ k) (h2 : k < 1189) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1178 then cr_1168_1178 k h1 h else cr_1178_1189 k (by omega) h2
theorem cr_1148_1189 (k : ℕ) (h1 : 1148 ≤ k) (h2 : k < 1189) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1168 then cr_1148_1168 k h1 h else cr_1168_1189 k (by omega) h2
theorem cr_1189_1190 (k : ℕ) (h1 : 1189 ≤ k) (h2 : k < 1190) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1189 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1189_ok
theorem cr_1190_1191 (k : ℕ) (h1 : 1190 ≤ k) (h2 : k < 1191) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1190 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1190_ok
theorem cr_1189_1191 (k : ℕ) (h1 : 1189 ≤ k) (h2 : k < 1191) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1190 then cr_1189_1190 k h1 h else cr_1190_1191 k (by omega) h2
theorem cr_1191_1192 (k : ℕ) (h1 : 1191 ≤ k) (h2 : k < 1192) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1191 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1191_ok
theorem cr_1192_1193 (k : ℕ) (h1 : 1192 ≤ k) (h2 : k < 1193) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1192 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1192_ok
theorem cr_1193_1194 (k : ℕ) (h1 : 1193 ≤ k) (h2 : k < 1194) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1193 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1193_ok
theorem cr_1192_1194 (k : ℕ) (h1 : 1192 ≤ k) (h2 : k < 1194) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1193 then cr_1192_1193 k h1 h else cr_1193_1194 k (by omega) h2
theorem cr_1191_1194 (k : ℕ) (h1 : 1191 ≤ k) (h2 : k < 1194) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1192 then cr_1191_1192 k h1 h else cr_1192_1194 k (by omega) h2
theorem cr_1189_1194 (k : ℕ) (h1 : 1189 ≤ k) (h2 : k < 1194) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1191 then cr_1189_1191 k h1 h else cr_1191_1194 k (by omega) h2
theorem cr_1194_1195 (k : ℕ) (h1 : 1194 ≤ k) (h2 : k < 1195) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1194 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1194_ok
theorem cr_1195_1196 (k : ℕ) (h1 : 1195 ≤ k) (h2 : k < 1196) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1195 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1195_ok
theorem cr_1194_1196 (k : ℕ) (h1 : 1194 ≤ k) (h2 : k < 1196) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1195 then cr_1194_1195 k h1 h else cr_1195_1196 k (by omega) h2
theorem cr_1196_1197 (k : ℕ) (h1 : 1196 ≤ k) (h2 : k < 1197) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1196 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1196_ok
theorem cr_1197_1198 (k : ℕ) (h1 : 1197 ≤ k) (h2 : k < 1198) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1197 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1197_ok
theorem cr_1198_1199 (k : ℕ) (h1 : 1198 ≤ k) (h2 : k < 1199) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1198 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1198_ok
theorem cr_1197_1199 (k : ℕ) (h1 : 1197 ≤ k) (h2 : k < 1199) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1198 then cr_1197_1198 k h1 h else cr_1198_1199 k (by omega) h2
theorem cr_1196_1199 (k : ℕ) (h1 : 1196 ≤ k) (h2 : k < 1199) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1197 then cr_1196_1197 k h1 h else cr_1197_1199 k (by omega) h2
theorem cr_1194_1199 (k : ℕ) (h1 : 1194 ≤ k) (h2 : k < 1199) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1196 then cr_1194_1196 k h1 h else cr_1196_1199 k (by omega) h2
theorem cr_1189_1199 (k : ℕ) (h1 : 1189 ≤ k) (h2 : k < 1199) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1194 then cr_1189_1194 k h1 h else cr_1194_1199 k (by omega) h2
theorem cr_1199_1200 (k : ℕ) (h1 : 1199 ≤ k) (h2 : k < 1200) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1199 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1199_ok
theorem cr_1200_1201 (k : ℕ) (h1 : 1200 ≤ k) (h2 : k < 1201) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1200 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1200_ok
theorem cr_1199_1201 (k : ℕ) (h1 : 1199 ≤ k) (h2 : k < 1201) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1200 then cr_1199_1200 k h1 h else cr_1200_1201 k (by omega) h2
theorem cr_1201_1202 (k : ℕ) (h1 : 1201 ≤ k) (h2 : k < 1202) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1201 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1201_ok
theorem cr_1202_1203 (k : ℕ) (h1 : 1202 ≤ k) (h2 : k < 1203) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1202 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1202_ok
theorem cr_1203_1204 (k : ℕ) (h1 : 1203 ≤ k) (h2 : k < 1204) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1203 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1203_ok
theorem cr_1202_1204 (k : ℕ) (h1 : 1202 ≤ k) (h2 : k < 1204) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1203 then cr_1202_1203 k h1 h else cr_1203_1204 k (by omega) h2
theorem cr_1201_1204 (k : ℕ) (h1 : 1201 ≤ k) (h2 : k < 1204) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1202 then cr_1201_1202 k h1 h else cr_1202_1204 k (by omega) h2
theorem cr_1199_1204 (k : ℕ) (h1 : 1199 ≤ k) (h2 : k < 1204) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1201 then cr_1199_1201 k h1 h else cr_1201_1204 k (by omega) h2
theorem cr_1204_1205 (k : ℕ) (h1 : 1204 ≤ k) (h2 : k < 1205) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1204 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1204_ok
theorem cr_1205_1206 (k : ℕ) (h1 : 1205 ≤ k) (h2 : k < 1206) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1205 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1205_ok
theorem cr_1204_1206 (k : ℕ) (h1 : 1204 ≤ k) (h2 : k < 1206) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1205 then cr_1204_1205 k h1 h else cr_1205_1206 k (by omega) h2
theorem cr_1206_1207 (k : ℕ) (h1 : 1206 ≤ k) (h2 : k < 1207) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1206 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1206_ok
theorem cr_1207_1208 (k : ℕ) (h1 : 1207 ≤ k) (h2 : k < 1208) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1207 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1207_ok
theorem cr_1208_1209 (k : ℕ) (h1 : 1208 ≤ k) (h2 : k < 1209) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1208 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1208_ok
theorem cr_1207_1209 (k : ℕ) (h1 : 1207 ≤ k) (h2 : k < 1209) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1208 then cr_1207_1208 k h1 h else cr_1208_1209 k (by omega) h2
theorem cr_1206_1209 (k : ℕ) (h1 : 1206 ≤ k) (h2 : k < 1209) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1207 then cr_1206_1207 k h1 h else cr_1207_1209 k (by omega) h2
theorem cr_1204_1209 (k : ℕ) (h1 : 1204 ≤ k) (h2 : k < 1209) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1206 then cr_1204_1206 k h1 h else cr_1206_1209 k (by omega) h2
theorem cr_1199_1209 (k : ℕ) (h1 : 1199 ≤ k) (h2 : k < 1209) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1204 then cr_1199_1204 k h1 h else cr_1204_1209 k (by omega) h2
theorem cr_1189_1209 (k : ℕ) (h1 : 1189 ≤ k) (h2 : k < 1209) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1199 then cr_1189_1199 k h1 h else cr_1199_1209 k (by omega) h2
theorem cr_1209_1210 (k : ℕ) (h1 : 1209 ≤ k) (h2 : k < 1210) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1209 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1209_ok
theorem cr_1210_1211 (k : ℕ) (h1 : 1210 ≤ k) (h2 : k < 1211) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1210 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1210_ok
theorem cr_1209_1211 (k : ℕ) (h1 : 1209 ≤ k) (h2 : k < 1211) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1210 then cr_1209_1210 k h1 h else cr_1210_1211 k (by omega) h2
theorem cr_1211_1212 (k : ℕ) (h1 : 1211 ≤ k) (h2 : k < 1212) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1211 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1211_ok
theorem cr_1212_1213 (k : ℕ) (h1 : 1212 ≤ k) (h2 : k < 1213) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1212 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1212_ok
theorem cr_1213_1214 (k : ℕ) (h1 : 1213 ≤ k) (h2 : k < 1214) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1213 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1213_ok
theorem cr_1212_1214 (k : ℕ) (h1 : 1212 ≤ k) (h2 : k < 1214) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1213 then cr_1212_1213 k h1 h else cr_1213_1214 k (by omega) h2
theorem cr_1211_1214 (k : ℕ) (h1 : 1211 ≤ k) (h2 : k < 1214) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1212 then cr_1211_1212 k h1 h else cr_1212_1214 k (by omega) h2
theorem cr_1209_1214 (k : ℕ) (h1 : 1209 ≤ k) (h2 : k < 1214) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1211 then cr_1209_1211 k h1 h else cr_1211_1214 k (by omega) h2
theorem cr_1214_1215 (k : ℕ) (h1 : 1214 ≤ k) (h2 : k < 1215) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1214 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1214_ok
theorem cr_1215_1216 (k : ℕ) (h1 : 1215 ≤ k) (h2 : k < 1216) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1215 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1215_ok
theorem cr_1214_1216 (k : ℕ) (h1 : 1214 ≤ k) (h2 : k < 1216) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1215 then cr_1214_1215 k h1 h else cr_1215_1216 k (by omega) h2
theorem cr_1216_1217 (k : ℕ) (h1 : 1216 ≤ k) (h2 : k < 1217) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1216 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1216_ok
theorem cr_1217_1218 (k : ℕ) (h1 : 1217 ≤ k) (h2 : k < 1218) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1217 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1217_ok
theorem cr_1218_1219 (k : ℕ) (h1 : 1218 ≤ k) (h2 : k < 1219) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1218 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1218_ok
theorem cr_1217_1219 (k : ℕ) (h1 : 1217 ≤ k) (h2 : k < 1219) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1218 then cr_1217_1218 k h1 h else cr_1218_1219 k (by omega) h2
theorem cr_1216_1219 (k : ℕ) (h1 : 1216 ≤ k) (h2 : k < 1219) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1217 then cr_1216_1217 k h1 h else cr_1217_1219 k (by omega) h2
theorem cr_1214_1219 (k : ℕ) (h1 : 1214 ≤ k) (h2 : k < 1219) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1216 then cr_1214_1216 k h1 h else cr_1216_1219 k (by omega) h2
theorem cr_1209_1219 (k : ℕ) (h1 : 1209 ≤ k) (h2 : k < 1219) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1214 then cr_1209_1214 k h1 h else cr_1214_1219 k (by omega) h2
theorem cr_1219_1220 (k : ℕ) (h1 : 1219 ≤ k) (h2 : k < 1220) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1219 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1219_ok
theorem cr_1220_1221 (k : ℕ) (h1 : 1220 ≤ k) (h2 : k < 1221) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1220 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1220_ok
theorem cr_1219_1221 (k : ℕ) (h1 : 1219 ≤ k) (h2 : k < 1221) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1220 then cr_1219_1220 k h1 h else cr_1220_1221 k (by omega) h2
theorem cr_1221_1222 (k : ℕ) (h1 : 1221 ≤ k) (h2 : k < 1222) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1221 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1221_ok
theorem cr_1222_1223 (k : ℕ) (h1 : 1222 ≤ k) (h2 : k < 1223) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1222 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1222_ok
theorem cr_1223_1224 (k : ℕ) (h1 : 1223 ≤ k) (h2 : k < 1224) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1223 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1223_ok
theorem cr_1222_1224 (k : ℕ) (h1 : 1222 ≤ k) (h2 : k < 1224) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1223 then cr_1222_1223 k h1 h else cr_1223_1224 k (by omega) h2
theorem cr_1221_1224 (k : ℕ) (h1 : 1221 ≤ k) (h2 : k < 1224) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1222 then cr_1221_1222 k h1 h else cr_1222_1224 k (by omega) h2
theorem cr_1219_1224 (k : ℕ) (h1 : 1219 ≤ k) (h2 : k < 1224) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1221 then cr_1219_1221 k h1 h else cr_1221_1224 k (by omega) h2
theorem cr_1224_1225 (k : ℕ) (h1 : 1224 ≤ k) (h2 : k < 1225) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1224 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1224_ok
theorem cr_1225_1226 (k : ℕ) (h1 : 1225 ≤ k) (h2 : k < 1226) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1225 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1225_ok
theorem cr_1226_1227 (k : ℕ) (h1 : 1226 ≤ k) (h2 : k < 1227) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1226 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1226_ok
theorem cr_1225_1227 (k : ℕ) (h1 : 1225 ≤ k) (h2 : k < 1227) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1226 then cr_1225_1226 k h1 h else cr_1226_1227 k (by omega) h2
theorem cr_1224_1227 (k : ℕ) (h1 : 1224 ≤ k) (h2 : k < 1227) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1225 then cr_1224_1225 k h1 h else cr_1225_1227 k (by omega) h2
theorem cr_1227_1228 (k : ℕ) (h1 : 1227 ≤ k) (h2 : k < 1228) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1227 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1227_ok
theorem cr_1228_1229 (k : ℕ) (h1 : 1228 ≤ k) (h2 : k < 1229) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1228 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1228_ok
theorem cr_1229_1230 (k : ℕ) (h1 : 1229 ≤ k) (h2 : k < 1230) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1229 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1229_ok
theorem cr_1228_1230 (k : ℕ) (h1 : 1228 ≤ k) (h2 : k < 1230) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1229 then cr_1228_1229 k h1 h else cr_1229_1230 k (by omega) h2
theorem cr_1227_1230 (k : ℕ) (h1 : 1227 ≤ k) (h2 : k < 1230) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1228 then cr_1227_1228 k h1 h else cr_1228_1230 k (by omega) h2
theorem cr_1224_1230 (k : ℕ) (h1 : 1224 ≤ k) (h2 : k < 1230) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1227 then cr_1224_1227 k h1 h else cr_1227_1230 k (by omega) h2
theorem cr_1219_1230 (k : ℕ) (h1 : 1219 ≤ k) (h2 : k < 1230) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1224 then cr_1219_1224 k h1 h else cr_1224_1230 k (by omega) h2
theorem cr_1209_1230 (k : ℕ) (h1 : 1209 ≤ k) (h2 : k < 1230) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1219 then cr_1209_1219 k h1 h else cr_1219_1230 k (by omega) h2
theorem cr_1189_1230 (k : ℕ) (h1 : 1189 ≤ k) (h2 : k < 1230) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1209 then cr_1189_1209 k h1 h else cr_1209_1230 k (by omega) h2
theorem cr_1148_1230 (k : ℕ) (h1 : 1148 ≤ k) (h2 : k < 1230) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1189 then cr_1148_1189 k h1 h else cr_1189_1230 k (by omega) h2
theorem cr_1230_1231 (k : ℕ) (h1 : 1230 ≤ k) (h2 : k < 1231) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1230 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1230_ok
theorem cr_1231_1232 (k : ℕ) (h1 : 1231 ≤ k) (h2 : k < 1232) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1231 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1231_ok
theorem cr_1230_1232 (k : ℕ) (h1 : 1230 ≤ k) (h2 : k < 1232) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1231 then cr_1230_1231 k h1 h else cr_1231_1232 k (by omega) h2
theorem cr_1232_1233 (k : ℕ) (h1 : 1232 ≤ k) (h2 : k < 1233) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1232 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1232_ok
theorem cr_1233_1234 (k : ℕ) (h1 : 1233 ≤ k) (h2 : k < 1234) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1233 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1233_ok
theorem cr_1234_1235 (k : ℕ) (h1 : 1234 ≤ k) (h2 : k < 1235) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1234 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1234_ok
theorem cr_1233_1235 (k : ℕ) (h1 : 1233 ≤ k) (h2 : k < 1235) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1234 then cr_1233_1234 k h1 h else cr_1234_1235 k (by omega) h2
theorem cr_1232_1235 (k : ℕ) (h1 : 1232 ≤ k) (h2 : k < 1235) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1233 then cr_1232_1233 k h1 h else cr_1233_1235 k (by omega) h2
theorem cr_1230_1235 (k : ℕ) (h1 : 1230 ≤ k) (h2 : k < 1235) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1232 then cr_1230_1232 k h1 h else cr_1232_1235 k (by omega) h2
theorem cr_1235_1236 (k : ℕ) (h1 : 1235 ≤ k) (h2 : k < 1236) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1235 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1235_ok
theorem cr_1236_1237 (k : ℕ) (h1 : 1236 ≤ k) (h2 : k < 1237) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1236 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1236_ok
theorem cr_1235_1237 (k : ℕ) (h1 : 1235 ≤ k) (h2 : k < 1237) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1236 then cr_1235_1236 k h1 h else cr_1236_1237 k (by omega) h2
theorem cr_1237_1238 (k : ℕ) (h1 : 1237 ≤ k) (h2 : k < 1238) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1237 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1237_ok
theorem cr_1238_1239 (k : ℕ) (h1 : 1238 ≤ k) (h2 : k < 1239) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1238 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1238_ok
theorem cr_1239_1240 (k : ℕ) (h1 : 1239 ≤ k) (h2 : k < 1240) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1239 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1239_ok
theorem cr_1238_1240 (k : ℕ) (h1 : 1238 ≤ k) (h2 : k < 1240) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1239 then cr_1238_1239 k h1 h else cr_1239_1240 k (by omega) h2
theorem cr_1237_1240 (k : ℕ) (h1 : 1237 ≤ k) (h2 : k < 1240) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1238 then cr_1237_1238 k h1 h else cr_1238_1240 k (by omega) h2
theorem cr_1235_1240 (k : ℕ) (h1 : 1235 ≤ k) (h2 : k < 1240) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1237 then cr_1235_1237 k h1 h else cr_1237_1240 k (by omega) h2
theorem cr_1230_1240 (k : ℕ) (h1 : 1230 ≤ k) (h2 : k < 1240) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1235 then cr_1230_1235 k h1 h else cr_1235_1240 k (by omega) h2
theorem cr_1240_1241 (k : ℕ) (h1 : 1240 ≤ k) (h2 : k < 1241) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1240 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1240_ok
theorem cr_1241_1242 (k : ℕ) (h1 : 1241 ≤ k) (h2 : k < 1242) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1241 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1241_ok
theorem cr_1240_1242 (k : ℕ) (h1 : 1240 ≤ k) (h2 : k < 1242) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1241 then cr_1240_1241 k h1 h else cr_1241_1242 k (by omega) h2
theorem cr_1242_1243 (k : ℕ) (h1 : 1242 ≤ k) (h2 : k < 1243) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1242 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1242_ok
theorem cr_1243_1244 (k : ℕ) (h1 : 1243 ≤ k) (h2 : k < 1244) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1243 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1243_ok
theorem cr_1244_1245 (k : ℕ) (h1 : 1244 ≤ k) (h2 : k < 1245) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1244 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1244_ok
theorem cr_1243_1245 (k : ℕ) (h1 : 1243 ≤ k) (h2 : k < 1245) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1244 then cr_1243_1244 k h1 h else cr_1244_1245 k (by omega) h2
theorem cr_1242_1245 (k : ℕ) (h1 : 1242 ≤ k) (h2 : k < 1245) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1243 then cr_1242_1243 k h1 h else cr_1243_1245 k (by omega) h2
theorem cr_1240_1245 (k : ℕ) (h1 : 1240 ≤ k) (h2 : k < 1245) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1242 then cr_1240_1242 k h1 h else cr_1242_1245 k (by omega) h2
theorem cr_1245_1246 (k : ℕ) (h1 : 1245 ≤ k) (h2 : k < 1246) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1245 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1245_ok
theorem cr_1246_1247 (k : ℕ) (h1 : 1246 ≤ k) (h2 : k < 1247) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1246 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1246_ok
theorem cr_1245_1247 (k : ℕ) (h1 : 1245 ≤ k) (h2 : k < 1247) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1246 then cr_1245_1246 k h1 h else cr_1246_1247 k (by omega) h2
theorem cr_1247_1248 (k : ℕ) (h1 : 1247 ≤ k) (h2 : k < 1248) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1247 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1247_ok
theorem cr_1248_1249 (k : ℕ) (h1 : 1248 ≤ k) (h2 : k < 1249) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1248 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1248_ok
theorem cr_1249_1250 (k : ℕ) (h1 : 1249 ≤ k) (h2 : k < 1250) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1249 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1249_ok
theorem cr_1248_1250 (k : ℕ) (h1 : 1248 ≤ k) (h2 : k < 1250) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1249 then cr_1248_1249 k h1 h else cr_1249_1250 k (by omega) h2
theorem cr_1247_1250 (k : ℕ) (h1 : 1247 ≤ k) (h2 : k < 1250) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1248 then cr_1247_1248 k h1 h else cr_1248_1250 k (by omega) h2
theorem cr_1245_1250 (k : ℕ) (h1 : 1245 ≤ k) (h2 : k < 1250) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1247 then cr_1245_1247 k h1 h else cr_1247_1250 k (by omega) h2
theorem cr_1240_1250 (k : ℕ) (h1 : 1240 ≤ k) (h2 : k < 1250) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1245 then cr_1240_1245 k h1 h else cr_1245_1250 k (by omega) h2
theorem cr_1230_1250 (k : ℕ) (h1 : 1230 ≤ k) (h2 : k < 1250) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1240 then cr_1230_1240 k h1 h else cr_1240_1250 k (by omega) h2
theorem cr_1250_1251 (k : ℕ) (h1 : 1250 ≤ k) (h2 : k < 1251) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1250 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1250_ok
theorem cr_1251_1252 (k : ℕ) (h1 : 1251 ≤ k) (h2 : k < 1252) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1251 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1251_ok
theorem cr_1250_1252 (k : ℕ) (h1 : 1250 ≤ k) (h2 : k < 1252) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1251 then cr_1250_1251 k h1 h else cr_1251_1252 k (by omega) h2
theorem cr_1252_1253 (k : ℕ) (h1 : 1252 ≤ k) (h2 : k < 1253) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1252 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1252_ok
theorem cr_1253_1254 (k : ℕ) (h1 : 1253 ≤ k) (h2 : k < 1254) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1253 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1253_ok
theorem cr_1254_1255 (k : ℕ) (h1 : 1254 ≤ k) (h2 : k < 1255) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1254 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1254_ok
theorem cr_1253_1255 (k : ℕ) (h1 : 1253 ≤ k) (h2 : k < 1255) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1254 then cr_1253_1254 k h1 h else cr_1254_1255 k (by omega) h2
theorem cr_1252_1255 (k : ℕ) (h1 : 1252 ≤ k) (h2 : k < 1255) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1253 then cr_1252_1253 k h1 h else cr_1253_1255 k (by omega) h2
theorem cr_1250_1255 (k : ℕ) (h1 : 1250 ≤ k) (h2 : k < 1255) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1252 then cr_1250_1252 k h1 h else cr_1252_1255 k (by omega) h2
theorem cr_1255_1256 (k : ℕ) (h1 : 1255 ≤ k) (h2 : k < 1256) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1255 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1255_ok
theorem cr_1256_1257 (k : ℕ) (h1 : 1256 ≤ k) (h2 : k < 1257) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1256 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1256_ok
theorem cr_1255_1257 (k : ℕ) (h1 : 1255 ≤ k) (h2 : k < 1257) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1256 then cr_1255_1256 k h1 h else cr_1256_1257 k (by omega) h2
theorem cr_1257_1258 (k : ℕ) (h1 : 1257 ≤ k) (h2 : k < 1258) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1257 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1257_ok
theorem cr_1258_1259 (k : ℕ) (h1 : 1258 ≤ k) (h2 : k < 1259) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1258 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1258_ok
theorem cr_1259_1260 (k : ℕ) (h1 : 1259 ≤ k) (h2 : k < 1260) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1259 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1259_ok
theorem cr_1258_1260 (k : ℕ) (h1 : 1258 ≤ k) (h2 : k < 1260) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1259 then cr_1258_1259 k h1 h else cr_1259_1260 k (by omega) h2
theorem cr_1257_1260 (k : ℕ) (h1 : 1257 ≤ k) (h2 : k < 1260) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1258 then cr_1257_1258 k h1 h else cr_1258_1260 k (by omega) h2
theorem cr_1255_1260 (k : ℕ) (h1 : 1255 ≤ k) (h2 : k < 1260) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1257 then cr_1255_1257 k h1 h else cr_1257_1260 k (by omega) h2
theorem cr_1250_1260 (k : ℕ) (h1 : 1250 ≤ k) (h2 : k < 1260) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1255 then cr_1250_1255 k h1 h else cr_1255_1260 k (by omega) h2
theorem cr_1260_1261 (k : ℕ) (h1 : 1260 ≤ k) (h2 : k < 1261) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1260 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1260_ok
theorem cr_1261_1262 (k : ℕ) (h1 : 1261 ≤ k) (h2 : k < 1262) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1261 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1261_ok
theorem cr_1260_1262 (k : ℕ) (h1 : 1260 ≤ k) (h2 : k < 1262) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1261 then cr_1260_1261 k h1 h else cr_1261_1262 k (by omega) h2
theorem cr_1262_1263 (k : ℕ) (h1 : 1262 ≤ k) (h2 : k < 1263) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1262 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1262_ok
theorem cr_1263_1264 (k : ℕ) (h1 : 1263 ≤ k) (h2 : k < 1264) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1263 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1263_ok
theorem cr_1264_1265 (k : ℕ) (h1 : 1264 ≤ k) (h2 : k < 1265) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1264 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1264_ok
theorem cr_1263_1265 (k : ℕ) (h1 : 1263 ≤ k) (h2 : k < 1265) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1264 then cr_1263_1264 k h1 h else cr_1264_1265 k (by omega) h2
theorem cr_1262_1265 (k : ℕ) (h1 : 1262 ≤ k) (h2 : k < 1265) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1263 then cr_1262_1263 k h1 h else cr_1263_1265 k (by omega) h2
theorem cr_1260_1265 (k : ℕ) (h1 : 1260 ≤ k) (h2 : k < 1265) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1262 then cr_1260_1262 k h1 h else cr_1262_1265 k (by omega) h2
theorem cr_1265_1266 (k : ℕ) (h1 : 1265 ≤ k) (h2 : k < 1266) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1265 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1265_ok
theorem cr_1266_1267 (k : ℕ) (h1 : 1266 ≤ k) (h2 : k < 1267) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1266 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1266_ok
theorem cr_1267_1268 (k : ℕ) (h1 : 1267 ≤ k) (h2 : k < 1268) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1267 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1267_ok
theorem cr_1266_1268 (k : ℕ) (h1 : 1266 ≤ k) (h2 : k < 1268) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1267 then cr_1266_1267 k h1 h else cr_1267_1268 k (by omega) h2
theorem cr_1265_1268 (k : ℕ) (h1 : 1265 ≤ k) (h2 : k < 1268) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1266 then cr_1265_1266 k h1 h else cr_1266_1268 k (by omega) h2
theorem cr_1268_1269 (k : ℕ) (h1 : 1268 ≤ k) (h2 : k < 1269) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1268 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1268_ok
theorem cr_1269_1270 (k : ℕ) (h1 : 1269 ≤ k) (h2 : k < 1270) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1269 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1269_ok
theorem cr_1270_1271 (k : ℕ) (h1 : 1270 ≤ k) (h2 : k < 1271) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1270 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1270_ok
theorem cr_1269_1271 (k : ℕ) (h1 : 1269 ≤ k) (h2 : k < 1271) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1270 then cr_1269_1270 k h1 h else cr_1270_1271 k (by omega) h2
theorem cr_1268_1271 (k : ℕ) (h1 : 1268 ≤ k) (h2 : k < 1271) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1269 then cr_1268_1269 k h1 h else cr_1269_1271 k (by omega) h2
theorem cr_1265_1271 (k : ℕ) (h1 : 1265 ≤ k) (h2 : k < 1271) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1268 then cr_1265_1268 k h1 h else cr_1268_1271 k (by omega) h2
theorem cr_1260_1271 (k : ℕ) (h1 : 1260 ≤ k) (h2 : k < 1271) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1265 then cr_1260_1265 k h1 h else cr_1265_1271 k (by omega) h2
theorem cr_1250_1271 (k : ℕ) (h1 : 1250 ≤ k) (h2 : k < 1271) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1260 then cr_1250_1260 k h1 h else cr_1260_1271 k (by omega) h2
theorem cr_1230_1271 (k : ℕ) (h1 : 1230 ≤ k) (h2 : k < 1271) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1250 then cr_1230_1250 k h1 h else cr_1250_1271 k (by omega) h2
theorem cr_1271_1272 (k : ℕ) (h1 : 1271 ≤ k) (h2 : k < 1272) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1271 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1271_ok
theorem cr_1272_1273 (k : ℕ) (h1 : 1272 ≤ k) (h2 : k < 1273) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1272 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1272_ok
theorem cr_1271_1273 (k : ℕ) (h1 : 1271 ≤ k) (h2 : k < 1273) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1272 then cr_1271_1272 k h1 h else cr_1272_1273 k (by omega) h2
theorem cr_1273_1274 (k : ℕ) (h1 : 1273 ≤ k) (h2 : k < 1274) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1273 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1273_ok
theorem cr_1274_1275 (k : ℕ) (h1 : 1274 ≤ k) (h2 : k < 1275) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1274 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1274_ok
theorem cr_1275_1276 (k : ℕ) (h1 : 1275 ≤ k) (h2 : k < 1276) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1275 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1275_ok
theorem cr_1274_1276 (k : ℕ) (h1 : 1274 ≤ k) (h2 : k < 1276) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1275 then cr_1274_1275 k h1 h else cr_1275_1276 k (by omega) h2
theorem cr_1273_1276 (k : ℕ) (h1 : 1273 ≤ k) (h2 : k < 1276) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1274 then cr_1273_1274 k h1 h else cr_1274_1276 k (by omega) h2
theorem cr_1271_1276 (k : ℕ) (h1 : 1271 ≤ k) (h2 : k < 1276) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1273 then cr_1271_1273 k h1 h else cr_1273_1276 k (by omega) h2
theorem cr_1276_1277 (k : ℕ) (h1 : 1276 ≤ k) (h2 : k < 1277) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1276 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1276_ok
theorem cr_1277_1278 (k : ℕ) (h1 : 1277 ≤ k) (h2 : k < 1278) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1277 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1277_ok
theorem cr_1276_1278 (k : ℕ) (h1 : 1276 ≤ k) (h2 : k < 1278) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1277 then cr_1276_1277 k h1 h else cr_1277_1278 k (by omega) h2
theorem cr_1278_1279 (k : ℕ) (h1 : 1278 ≤ k) (h2 : k < 1279) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1278 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1278_ok
theorem cr_1279_1280 (k : ℕ) (h1 : 1279 ≤ k) (h2 : k < 1280) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1279 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1279_ok
theorem cr_1280_1281 (k : ℕ) (h1 : 1280 ≤ k) (h2 : k < 1281) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1280 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1280_ok
theorem cr_1279_1281 (k : ℕ) (h1 : 1279 ≤ k) (h2 : k < 1281) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1280 then cr_1279_1280 k h1 h else cr_1280_1281 k (by omega) h2
theorem cr_1278_1281 (k : ℕ) (h1 : 1278 ≤ k) (h2 : k < 1281) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1279 then cr_1278_1279 k h1 h else cr_1279_1281 k (by omega) h2
theorem cr_1276_1281 (k : ℕ) (h1 : 1276 ≤ k) (h2 : k < 1281) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1278 then cr_1276_1278 k h1 h else cr_1278_1281 k (by omega) h2
theorem cr_1271_1281 (k : ℕ) (h1 : 1271 ≤ k) (h2 : k < 1281) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1276 then cr_1271_1276 k h1 h else cr_1276_1281 k (by omega) h2
theorem cr_1281_1282 (k : ℕ) (h1 : 1281 ≤ k) (h2 : k < 1282) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1281 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1281_ok
theorem cr_1282_1283 (k : ℕ) (h1 : 1282 ≤ k) (h2 : k < 1283) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1282 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1282_ok
theorem cr_1281_1283 (k : ℕ) (h1 : 1281 ≤ k) (h2 : k < 1283) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1282 then cr_1281_1282 k h1 h else cr_1282_1283 k (by omega) h2
theorem cr_1283_1284 (k : ℕ) (h1 : 1283 ≤ k) (h2 : k < 1284) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1283 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1283_ok
theorem cr_1284_1285 (k : ℕ) (h1 : 1284 ≤ k) (h2 : k < 1285) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1284 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1284_ok
theorem cr_1285_1286 (k : ℕ) (h1 : 1285 ≤ k) (h2 : k < 1286) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1285 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1285_ok
theorem cr_1284_1286 (k : ℕ) (h1 : 1284 ≤ k) (h2 : k < 1286) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1285 then cr_1284_1285 k h1 h else cr_1285_1286 k (by omega) h2
theorem cr_1283_1286 (k : ℕ) (h1 : 1283 ≤ k) (h2 : k < 1286) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1284 then cr_1283_1284 k h1 h else cr_1284_1286 k (by omega) h2
theorem cr_1281_1286 (k : ℕ) (h1 : 1281 ≤ k) (h2 : k < 1286) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1283 then cr_1281_1283 k h1 h else cr_1283_1286 k (by omega) h2
theorem cr_1286_1287 (k : ℕ) (h1 : 1286 ≤ k) (h2 : k < 1287) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1286 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1286_ok
theorem cr_1287_1288 (k : ℕ) (h1 : 1287 ≤ k) (h2 : k < 1288) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1287 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1287_ok
theorem cr_1288_1289 (k : ℕ) (h1 : 1288 ≤ k) (h2 : k < 1289) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1288 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1288_ok
theorem cr_1287_1289 (k : ℕ) (h1 : 1287 ≤ k) (h2 : k < 1289) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1288 then cr_1287_1288 k h1 h else cr_1288_1289 k (by omega) h2
theorem cr_1286_1289 (k : ℕ) (h1 : 1286 ≤ k) (h2 : k < 1289) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1287 then cr_1286_1287 k h1 h else cr_1287_1289 k (by omega) h2
theorem cr_1289_1290 (k : ℕ) (h1 : 1289 ≤ k) (h2 : k < 1290) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1289 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1289_ok
theorem cr_1290_1291 (k : ℕ) (h1 : 1290 ≤ k) (h2 : k < 1291) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1290 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1290_ok
theorem cr_1291_1292 (k : ℕ) (h1 : 1291 ≤ k) (h2 : k < 1292) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1291 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1291_ok
theorem cr_1290_1292 (k : ℕ) (h1 : 1290 ≤ k) (h2 : k < 1292) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1291 then cr_1290_1291 k h1 h else cr_1291_1292 k (by omega) h2
theorem cr_1289_1292 (k : ℕ) (h1 : 1289 ≤ k) (h2 : k < 1292) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1290 then cr_1289_1290 k h1 h else cr_1290_1292 k (by omega) h2
theorem cr_1286_1292 (k : ℕ) (h1 : 1286 ≤ k) (h2 : k < 1292) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1289 then cr_1286_1289 k h1 h else cr_1289_1292 k (by omega) h2
theorem cr_1281_1292 (k : ℕ) (h1 : 1281 ≤ k) (h2 : k < 1292) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1286 then cr_1281_1286 k h1 h else cr_1286_1292 k (by omega) h2
theorem cr_1271_1292 (k : ℕ) (h1 : 1271 ≤ k) (h2 : k < 1292) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1281 then cr_1271_1281 k h1 h else cr_1281_1292 k (by omega) h2
theorem cr_1292_1293 (k : ℕ) (h1 : 1292 ≤ k) (h2 : k < 1293) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1292 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1292_ok
theorem cr_1293_1294 (k : ℕ) (h1 : 1293 ≤ k) (h2 : k < 1294) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1293 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1293_ok
theorem cr_1292_1294 (k : ℕ) (h1 : 1292 ≤ k) (h2 : k < 1294) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1293 then cr_1292_1293 k h1 h else cr_1293_1294 k (by omega) h2
theorem cr_1294_1295 (k : ℕ) (h1 : 1294 ≤ k) (h2 : k < 1295) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1294 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1294_ok
theorem cr_1295_1296 (k : ℕ) (h1 : 1295 ≤ k) (h2 : k < 1296) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1295 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1295_ok
theorem cr_1296_1297 (k : ℕ) (h1 : 1296 ≤ k) (h2 : k < 1297) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1296 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1296_ok
theorem cr_1295_1297 (k : ℕ) (h1 : 1295 ≤ k) (h2 : k < 1297) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1296 then cr_1295_1296 k h1 h else cr_1296_1297 k (by omega) h2
theorem cr_1294_1297 (k : ℕ) (h1 : 1294 ≤ k) (h2 : k < 1297) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1295 then cr_1294_1295 k h1 h else cr_1295_1297 k (by omega) h2
theorem cr_1292_1297 (k : ℕ) (h1 : 1292 ≤ k) (h2 : k < 1297) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1294 then cr_1292_1294 k h1 h else cr_1294_1297 k (by omega) h2
theorem cr_1297_1298 (k : ℕ) (h1 : 1297 ≤ k) (h2 : k < 1298) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1297 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1297_ok
theorem cr_1298_1299 (k : ℕ) (h1 : 1298 ≤ k) (h2 : k < 1299) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1298 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1298_ok
theorem cr_1297_1299 (k : ℕ) (h1 : 1297 ≤ k) (h2 : k < 1299) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1298 then cr_1297_1298 k h1 h else cr_1298_1299 k (by omega) h2
theorem cr_1299_1300 (k : ℕ) (h1 : 1299 ≤ k) (h2 : k < 1300) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1299 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1299_ok
theorem cr_1300_1301 (k : ℕ) (h1 : 1300 ≤ k) (h2 : k < 1301) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1300 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1300_ok
theorem cr_1301_1302 (k : ℕ) (h1 : 1301 ≤ k) (h2 : k < 1302) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1301 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1301_ok
theorem cr_1300_1302 (k : ℕ) (h1 : 1300 ≤ k) (h2 : k < 1302) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1301 then cr_1300_1301 k h1 h else cr_1301_1302 k (by omega) h2
theorem cr_1299_1302 (k : ℕ) (h1 : 1299 ≤ k) (h2 : k < 1302) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1300 then cr_1299_1300 k h1 h else cr_1300_1302 k (by omega) h2
theorem cr_1297_1302 (k : ℕ) (h1 : 1297 ≤ k) (h2 : k < 1302) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1299 then cr_1297_1299 k h1 h else cr_1299_1302 k (by omega) h2
theorem cr_1292_1302 (k : ℕ) (h1 : 1292 ≤ k) (h2 : k < 1302) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1297 then cr_1292_1297 k h1 h else cr_1297_1302 k (by omega) h2
theorem cr_1302_1303 (k : ℕ) (h1 : 1302 ≤ k) (h2 : k < 1303) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1302 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1302_ok
theorem cr_1303_1304 (k : ℕ) (h1 : 1303 ≤ k) (h2 : k < 1304) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1303 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1303_ok
theorem cr_1302_1304 (k : ℕ) (h1 : 1302 ≤ k) (h2 : k < 1304) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1303 then cr_1302_1303 k h1 h else cr_1303_1304 k (by omega) h2
theorem cr_1304_1305 (k : ℕ) (h1 : 1304 ≤ k) (h2 : k < 1305) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1304 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1304_ok
theorem cr_1305_1306 (k : ℕ) (h1 : 1305 ≤ k) (h2 : k < 1306) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1305 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1305_ok
theorem cr_1306_1307 (k : ℕ) (h1 : 1306 ≤ k) (h2 : k < 1307) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1306 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1306_ok
theorem cr_1305_1307 (k : ℕ) (h1 : 1305 ≤ k) (h2 : k < 1307) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1306 then cr_1305_1306 k h1 h else cr_1306_1307 k (by omega) h2
theorem cr_1304_1307 (k : ℕ) (h1 : 1304 ≤ k) (h2 : k < 1307) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1305 then cr_1304_1305 k h1 h else cr_1305_1307 k (by omega) h2
theorem cr_1302_1307 (k : ℕ) (h1 : 1302 ≤ k) (h2 : k < 1307) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1304 then cr_1302_1304 k h1 h else cr_1304_1307 k (by omega) h2
theorem cr_1307_1308 (k : ℕ) (h1 : 1307 ≤ k) (h2 : k < 1308) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1307 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1307_ok
theorem cr_1308_1309 (k : ℕ) (h1 : 1308 ≤ k) (h2 : k < 1309) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1308 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1308_ok
theorem cr_1309_1310 (k : ℕ) (h1 : 1309 ≤ k) (h2 : k < 1310) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1309 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1309_ok
theorem cr_1308_1310 (k : ℕ) (h1 : 1308 ≤ k) (h2 : k < 1310) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1309 then cr_1308_1309 k h1 h else cr_1309_1310 k (by omega) h2
theorem cr_1307_1310 (k : ℕ) (h1 : 1307 ≤ k) (h2 : k < 1310) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1308 then cr_1307_1308 k h1 h else cr_1308_1310 k (by omega) h2
theorem cr_1310_1311 (k : ℕ) (h1 : 1310 ≤ k) (h2 : k < 1311) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1310 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1310_ok
theorem cr_1311_1312 (k : ℕ) (h1 : 1311 ≤ k) (h2 : k < 1312) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1311 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1311_ok
theorem cr_1312_1313 (k : ℕ) (h1 : 1312 ≤ k) (h2 : k < 1313) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1312 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1312_ok
theorem cr_1311_1313 (k : ℕ) (h1 : 1311 ≤ k) (h2 : k < 1313) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1312 then cr_1311_1312 k h1 h else cr_1312_1313 k (by omega) h2
theorem cr_1310_1313 (k : ℕ) (h1 : 1310 ≤ k) (h2 : k < 1313) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1311 then cr_1310_1311 k h1 h else cr_1311_1313 k (by omega) h2
theorem cr_1307_1313 (k : ℕ) (h1 : 1307 ≤ k) (h2 : k < 1313) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1310 then cr_1307_1310 k h1 h else cr_1310_1313 k (by omega) h2
theorem cr_1302_1313 (k : ℕ) (h1 : 1302 ≤ k) (h2 : k < 1313) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1307 then cr_1302_1307 k h1 h else cr_1307_1313 k (by omega) h2
theorem cr_1292_1313 (k : ℕ) (h1 : 1292 ≤ k) (h2 : k < 1313) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1302 then cr_1292_1302 k h1 h else cr_1302_1313 k (by omega) h2
theorem cr_1271_1313 (k : ℕ) (h1 : 1271 ≤ k) (h2 : k < 1313) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1292 then cr_1271_1292 k h1 h else cr_1292_1313 k (by omega) h2
theorem cr_1230_1313 (k : ℕ) (h1 : 1230 ≤ k) (h2 : k < 1313) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1271 then cr_1230_1271 k h1 h else cr_1271_1313 k (by omega) h2
theorem cr_1148_1313 (k : ℕ) (h1 : 1148 ≤ k) (h2 : k < 1313) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1230 then cr_1148_1230 k h1 h else cr_1230_1313 k (by omega) h2
theorem cr_984_1313 (k : ℕ) (h1 : 984 ≤ k) (h2 : k < 1313) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1148 then cr_984_1148 k h1 h else cr_1148_1313 k (by omega) h2
theorem cr_656_1313 (k : ℕ) (h1 : 656 ≤ k) (h2 : k < 1313) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 984 then cr_656_984 k h1 h else cr_984_1313 k (by omega) h2

end Harris
