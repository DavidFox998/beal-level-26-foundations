import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1460
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1461
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1462
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1463
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1464
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1465
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1466
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1467
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1468
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1469

namespace BealMatveevBeal.BealMatveevBealV25B0Search.Chunked10e6

set_option maxRecDepth 4096
set_option maxHeartbeats 0

/-- Ten separate kernel-checked 500-value intervals. -/
theorem group_146 (i : ℕ) (hi : i < 10) :
    checkRange (500 * (10 * 146 + i)) (500 * (10 * 146 + i + 1)) = true := by
  by_cases h0 : i = 0
  · subst i
    exact chunk_1460
  by_cases h1 : i = 1
  · subst i
    exact chunk_1461
  by_cases h2 : i = 2
  · subst i
    exact chunk_1462
  by_cases h3 : i = 3
  · subst i
    exact chunk_1463
  by_cases h4 : i = 4
  · subst i
    exact chunk_1464
  by_cases h5 : i = 5
  · subst i
    exact chunk_1465
  by_cases h6 : i = 6
  · subst i
    exact chunk_1466
  by_cases h7 : i = 7
  · subst i
    exact chunk_1467
  by_cases h8 : i = 8
  · subst i
    exact chunk_1468
  by_cases h9 : i = 9
  · subst i
    exact chunk_1469
  omega

end BealMatveevBeal.BealMatveevBealV25B0Search.Chunked10e6
