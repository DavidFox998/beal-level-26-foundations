import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1590
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1591
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1592
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1593
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1594
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1595
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1596
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1597
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1598
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1599

namespace BealMatveevBeal.BealMatveevBealV25B0Search.Chunked10e6

set_option maxRecDepth 4096
set_option maxHeartbeats 0

/-- Ten separate kernel-checked 500-value intervals. -/
theorem group_159 (i : ℕ) (hi : i < 10) :
    checkRange (500 * (10 * 159 + i)) (500 * (10 * 159 + i + 1)) = true := by
  by_cases h0 : i = 0
  · subst i
    exact chunk_1590
  by_cases h1 : i = 1
  · subst i
    exact chunk_1591
  by_cases h2 : i = 2
  · subst i
    exact chunk_1592
  by_cases h3 : i = 3
  · subst i
    exact chunk_1593
  by_cases h4 : i = 4
  · subst i
    exact chunk_1594
  by_cases h5 : i = 5
  · subst i
    exact chunk_1595
  by_cases h6 : i = 6
  · subst i
    exact chunk_1596
  by_cases h7 : i = 7
  · subst i
    exact chunk_1597
  by_cases h8 : i = 8
  · subst i
    exact chunk_1598
  by_cases h9 : i = 9
  · subst i
    exact chunk_1599
  omega

end BealMatveevBeal.BealMatveevBealV25B0Search.Chunked10e6
