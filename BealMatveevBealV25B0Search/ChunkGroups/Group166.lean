import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1660
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1661
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1662
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1663
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1664
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1665
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1666
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1667
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1668
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1669

namespace BealMatveevBeal.BealMatveevBealV25B0Search.Chunked10e6

set_option maxRecDepth 4096
set_option maxHeartbeats 0

/-- Ten separate kernel-checked 500-value intervals. -/
theorem group_166 (i : ℕ) (hi : i < 10) :
    checkRange (500 * (10 * 166 + i)) (500 * (10 * 166 + i + 1)) = true := by
  by_cases h0 : i = 0
  · subst i
    exact chunk_1660
  by_cases h1 : i = 1
  · subst i
    exact chunk_1661
  by_cases h2 : i = 2
  · subst i
    exact chunk_1662
  by_cases h3 : i = 3
  · subst i
    exact chunk_1663
  by_cases h4 : i = 4
  · subst i
    exact chunk_1664
  by_cases h5 : i = 5
  · subst i
    exact chunk_1665
  by_cases h6 : i = 6
  · subst i
    exact chunk_1666
  by_cases h7 : i = 7
  · subst i
    exact chunk_1667
  by_cases h8 : i = 8
  · subst i
    exact chunk_1668
  by_cases h9 : i = 9
  · subst i
    exact chunk_1669
  omega

end BealMatveevBeal.BealMatveevBealV25B0Search.Chunked10e6
