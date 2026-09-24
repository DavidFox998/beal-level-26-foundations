import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1560
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1561
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1562
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1563
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1564
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1565
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1566
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1567
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1568
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1569

namespace BealMatveevBeal.BealMatveevBealV25B0Search.Chunked10e6

set_option maxRecDepth 4096
set_option maxHeartbeats 0

/-- Ten separate kernel-checked 500-value intervals. -/
theorem group_156 (i : ℕ) (hi : i < 10) :
    checkRange (500 * (10 * 156 + i)) (500 * (10 * 156 + i + 1)) = true := by
  by_cases h0 : i = 0
  · subst i
    exact chunk_1560
  by_cases h1 : i = 1
  · subst i
    exact chunk_1561
  by_cases h2 : i = 2
  · subst i
    exact chunk_1562
  by_cases h3 : i = 3
  · subst i
    exact chunk_1563
  by_cases h4 : i = 4
  · subst i
    exact chunk_1564
  by_cases h5 : i = 5
  · subst i
    exact chunk_1565
  by_cases h6 : i = 6
  · subst i
    exact chunk_1566
  by_cases h7 : i = 7
  · subst i
    exact chunk_1567
  by_cases h8 : i = 8
  · subst i
    exact chunk_1568
  by_cases h9 : i = 9
  · subst i
    exact chunk_1569
  omega

end BealMatveevBeal.BealMatveevBealV25B0Search.Chunked10e6
