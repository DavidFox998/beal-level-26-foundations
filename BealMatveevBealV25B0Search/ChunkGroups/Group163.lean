import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1630
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1631
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1632
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1633
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1634
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1635
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1636
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1637
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1638
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1639

namespace BealMatveevBeal.BealMatveevBealV25B0Search.Chunked10e6

set_option maxRecDepth 4096
set_option maxHeartbeats 0

/-- Ten separate kernel-checked 500-value intervals. -/
theorem group_163 (i : ℕ) (hi : i < 10) :
    checkRange (500 * (10 * 163 + i)) (500 * (10 * 163 + i + 1)) = true := by
  by_cases h0 : i = 0
  · subst i
    exact chunk_1630
  by_cases h1 : i = 1
  · subst i
    exact chunk_1631
  by_cases h2 : i = 2
  · subst i
    exact chunk_1632
  by_cases h3 : i = 3
  · subst i
    exact chunk_1633
  by_cases h4 : i = 4
  · subst i
    exact chunk_1634
  by_cases h5 : i = 5
  · subst i
    exact chunk_1635
  by_cases h6 : i = 6
  · subst i
    exact chunk_1636
  by_cases h7 : i = 7
  · subst i
    exact chunk_1637
  by_cases h8 : i = 8
  · subst i
    exact chunk_1638
  by_cases h9 : i = 9
  · subst i
    exact chunk_1639
  omega

end BealMatveevBeal.BealMatveevBealV25B0Search.Chunked10e6
