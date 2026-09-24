import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1540
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1541
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1542
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1543
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1544
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1545
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1546
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1547
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1548
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1549

namespace BealMatveevBeal.BealMatveevBealV25B0Search.Chunked10e6

set_option maxRecDepth 4096
set_option maxHeartbeats 0

/-- Ten separate kernel-checked 500-value intervals. -/
theorem group_154 (i : ℕ) (hi : i < 10) :
    checkRange (500 * (10 * 154 + i)) (500 * (10 * 154 + i + 1)) = true := by
  by_cases h0 : i = 0
  · subst i
    exact chunk_1540
  by_cases h1 : i = 1
  · subst i
    exact chunk_1541
  by_cases h2 : i = 2
  · subst i
    exact chunk_1542
  by_cases h3 : i = 3
  · subst i
    exact chunk_1543
  by_cases h4 : i = 4
  · subst i
    exact chunk_1544
  by_cases h5 : i = 5
  · subst i
    exact chunk_1545
  by_cases h6 : i = 6
  · subst i
    exact chunk_1546
  by_cases h7 : i = 7
  · subst i
    exact chunk_1547
  by_cases h8 : i = 8
  · subst i
    exact chunk_1548
  by_cases h9 : i = 9
  · subst i
    exact chunk_1549
  omega

end BealMatveevBeal.BealMatveevBealV25B0Search.Chunked10e6
