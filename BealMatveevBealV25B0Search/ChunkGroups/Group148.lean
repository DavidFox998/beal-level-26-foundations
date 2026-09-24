import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1480
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1481
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1482
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1483
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1484
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1485
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1486
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1487
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1488
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1489

namespace BealMatveevBeal.BealMatveevBealV25B0Search.Chunked10e6

set_option maxRecDepth 4096
set_option maxHeartbeats 0

/-- Ten separate kernel-checked 500-value intervals. -/
theorem group_148 (i : ℕ) (hi : i < 10) :
    checkRange (500 * (10 * 148 + i)) (500 * (10 * 148 + i + 1)) = true := by
  by_cases h0 : i = 0
  · subst i
    exact chunk_1480
  by_cases h1 : i = 1
  · subst i
    exact chunk_1481
  by_cases h2 : i = 2
  · subst i
    exact chunk_1482
  by_cases h3 : i = 3
  · subst i
    exact chunk_1483
  by_cases h4 : i = 4
  · subst i
    exact chunk_1484
  by_cases h5 : i = 5
  · subst i
    exact chunk_1485
  by_cases h6 : i = 6
  · subst i
    exact chunk_1486
  by_cases h7 : i = 7
  · subst i
    exact chunk_1487
  by_cases h8 : i = 8
  · subst i
    exact chunk_1488
  by_cases h9 : i = 9
  · subst i
    exact chunk_1489
  omega

end BealMatveevBeal.BealMatveevBealV25B0Search.Chunked10e6
