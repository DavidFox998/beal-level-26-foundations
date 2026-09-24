import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1510
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1511
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1512
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1513
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1514
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1515
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1516
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1517
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1518
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1519

namespace BealMatveevBeal.BealMatveevBealV25B0Search.Chunked10e6

set_option maxRecDepth 4096
set_option maxHeartbeats 0

/-- Ten separate kernel-checked 500-value intervals. -/
theorem group_151 (i : ℕ) (hi : i < 10) :
    checkRange (500 * (10 * 151 + i)) (500 * (10 * 151 + i + 1)) = true := by
  by_cases h0 : i = 0
  · subst i
    exact chunk_1510
  by_cases h1 : i = 1
  · subst i
    exact chunk_1511
  by_cases h2 : i = 2
  · subst i
    exact chunk_1512
  by_cases h3 : i = 3
  · subst i
    exact chunk_1513
  by_cases h4 : i = 4
  · subst i
    exact chunk_1514
  by_cases h5 : i = 5
  · subst i
    exact chunk_1515
  by_cases h6 : i = 6
  · subst i
    exact chunk_1516
  by_cases h7 : i = 7
  · subst i
    exact chunk_1517
  by_cases h8 : i = 8
  · subst i
    exact chunk_1518
  by_cases h9 : i = 9
  · subst i
    exact chunk_1519
  omega

end BealMatveevBeal.BealMatveevBealV25B0Search.Chunked10e6
