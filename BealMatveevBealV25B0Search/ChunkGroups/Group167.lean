import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1670
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1671
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1672
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1673
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1674
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1675
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1676
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1677
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1678
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1679

namespace BealMatveevBeal.BealMatveevBealV25B0Search.Chunked10e6

set_option maxRecDepth 4096
set_option maxHeartbeats 0

/-- Ten separate kernel-checked 500-value intervals. -/
theorem group_167 (i : ℕ) (hi : i < 10) :
    checkRange (500 * (10 * 167 + i)) (500 * (10 * 167 + i + 1)) = true := by
  by_cases h0 : i = 0
  · subst i
    exact chunk_1670
  by_cases h1 : i = 1
  · subst i
    exact chunk_1671
  by_cases h2 : i = 2
  · subst i
    exact chunk_1672
  by_cases h3 : i = 3
  · subst i
    exact chunk_1673
  by_cases h4 : i = 4
  · subst i
    exact chunk_1674
  by_cases h5 : i = 5
  · subst i
    exact chunk_1675
  by_cases h6 : i = 6
  · subst i
    exact chunk_1676
  by_cases h7 : i = 7
  · subst i
    exact chunk_1677
  by_cases h8 : i = 8
  · subst i
    exact chunk_1678
  by_cases h9 : i = 9
  · subst i
    exact chunk_1679
  omega

end BealMatveevBeal.BealMatveevBealV25B0Search.Chunked10e6
