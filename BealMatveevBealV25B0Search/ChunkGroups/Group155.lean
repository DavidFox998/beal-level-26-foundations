import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1550
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1551
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1552
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1553
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1554
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1555
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1556
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1557
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1558
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1559

namespace BealMatveevBeal.BealMatveevBealV25B0Search.Chunked10e6

set_option maxRecDepth 4096
set_option maxHeartbeats 0

/-- Ten separate kernel-checked 500-value intervals. -/
theorem group_155 (i : ℕ) (hi : i < 10) :
    checkRange (500 * (10 * 155 + i)) (500 * (10 * 155 + i + 1)) = true := by
  by_cases h0 : i = 0
  · subst i
    exact chunk_1550
  by_cases h1 : i = 1
  · subst i
    exact chunk_1551
  by_cases h2 : i = 2
  · subst i
    exact chunk_1552
  by_cases h3 : i = 3
  · subst i
    exact chunk_1553
  by_cases h4 : i = 4
  · subst i
    exact chunk_1554
  by_cases h5 : i = 5
  · subst i
    exact chunk_1555
  by_cases h6 : i = 6
  · subst i
    exact chunk_1556
  by_cases h7 : i = 7
  · subst i
    exact chunk_1557
  by_cases h8 : i = 8
  · subst i
    exact chunk_1558
  by_cases h9 : i = 9
  · subst i
    exact chunk_1559
  omega

end BealMatveevBeal.BealMatveevBealV25B0Search.Chunked10e6
