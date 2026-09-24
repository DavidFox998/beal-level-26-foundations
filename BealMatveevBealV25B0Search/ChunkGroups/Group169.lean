import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1690
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1691
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1692
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1693
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1694
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1695
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1696
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1697
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1698
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1699

namespace BealMatveevBeal.BealMatveevBealV25B0Search.Chunked10e6

set_option maxRecDepth 4096
set_option maxHeartbeats 0

/-- Ten separate kernel-checked 500-value intervals. -/
theorem group_169 (i : ℕ) (hi : i < 10) :
    checkRange (500 * (10 * 169 + i)) (500 * (10 * 169 + i + 1)) = true := by
  by_cases h0 : i = 0
  · subst i
    exact chunk_1690
  by_cases h1 : i = 1
  · subst i
    exact chunk_1691
  by_cases h2 : i = 2
  · subst i
    exact chunk_1692
  by_cases h3 : i = 3
  · subst i
    exact chunk_1693
  by_cases h4 : i = 4
  · subst i
    exact chunk_1694
  by_cases h5 : i = 5
  · subst i
    exact chunk_1695
  by_cases h6 : i = 6
  · subst i
    exact chunk_1696
  by_cases h7 : i = 7
  · subst i
    exact chunk_1697
  by_cases h8 : i = 8
  · subst i
    exact chunk_1698
  by_cases h9 : i = 9
  · subst i
    exact chunk_1699
  omega

end BealMatveevBeal.BealMatveevBealV25B0Search.Chunked10e6
