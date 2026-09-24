import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1680
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1681
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1682
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1683
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1684
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1685
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1686
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1687
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1688
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1689

namespace BealMatveevBeal.BealMatveevBealV25B0Search.Chunked10e6

set_option maxRecDepth 4096
set_option maxHeartbeats 0

/-- Ten separate kernel-checked 500-value intervals. -/
theorem group_168 (i : ℕ) (hi : i < 10) :
    checkRange (500 * (10 * 168 + i)) (500 * (10 * 168 + i + 1)) = true := by
  by_cases h0 : i = 0
  · subst i
    exact chunk_1680
  by_cases h1 : i = 1
  · subst i
    exact chunk_1681
  by_cases h2 : i = 2
  · subst i
    exact chunk_1682
  by_cases h3 : i = 3
  · subst i
    exact chunk_1683
  by_cases h4 : i = 4
  · subst i
    exact chunk_1684
  by_cases h5 : i = 5
  · subst i
    exact chunk_1685
  by_cases h6 : i = 6
  · subst i
    exact chunk_1686
  by_cases h7 : i = 7
  · subst i
    exact chunk_1687
  by_cases h8 : i = 8
  · subst i
    exact chunk_1688
  by_cases h9 : i = 9
  · subst i
    exact chunk_1689
  omega

end BealMatveevBeal.BealMatveevBealV25B0Search.Chunked10e6
