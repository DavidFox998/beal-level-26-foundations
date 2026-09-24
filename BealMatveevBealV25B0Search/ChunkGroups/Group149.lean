import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1490
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1491
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1492
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1493
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1494
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1495
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1496
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1497
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1498
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1499

namespace BealMatveevBeal.BealMatveevBealV25B0Search.Chunked10e6

set_option maxRecDepth 4096
set_option maxHeartbeats 0

/-- Ten separate kernel-checked 500-value intervals. -/
theorem group_149 (i : ℕ) (hi : i < 10) :
    checkRange (500 * (10 * 149 + i)) (500 * (10 * 149 + i + 1)) = true := by
  by_cases h0 : i = 0
  · subst i
    exact chunk_1490
  by_cases h1 : i = 1
  · subst i
    exact chunk_1491
  by_cases h2 : i = 2
  · subst i
    exact chunk_1492
  by_cases h3 : i = 3
  · subst i
    exact chunk_1493
  by_cases h4 : i = 4
  · subst i
    exact chunk_1494
  by_cases h5 : i = 5
  · subst i
    exact chunk_1495
  by_cases h6 : i = 6
  · subst i
    exact chunk_1496
  by_cases h7 : i = 7
  · subst i
    exact chunk_1497
  by_cases h8 : i = 8
  · subst i
    exact chunk_1498
  by_cases h9 : i = 9
  · subst i
    exact chunk_1499
  omega

end BealMatveevBeal.BealMatveevBealV25B0Search.Chunked10e6
