import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1600
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1601
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1602
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1603
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1604
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1605
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1606
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1607
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1608
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1609

namespace BealMatveevBeal.BealMatveevBealV25B0Search.Chunked10e6

set_option maxRecDepth 4096
set_option maxHeartbeats 0

/-- Ten separate kernel-checked 500-value intervals. -/
theorem group_160 (i : ℕ) (hi : i < 10) :
    checkRange (500 * (10 * 160 + i)) (500 * (10 * 160 + i + 1)) = true := by
  by_cases h0 : i = 0
  · subst i
    exact chunk_1600
  by_cases h1 : i = 1
  · subst i
    exact chunk_1601
  by_cases h2 : i = 2
  · subst i
    exact chunk_1602
  by_cases h3 : i = 3
  · subst i
    exact chunk_1603
  by_cases h4 : i = 4
  · subst i
    exact chunk_1604
  by_cases h5 : i = 5
  · subst i
    exact chunk_1605
  by_cases h6 : i = 6
  · subst i
    exact chunk_1606
  by_cases h7 : i = 7
  · subst i
    exact chunk_1607
  by_cases h8 : i = 8
  · subst i
    exact chunk_1608
  by_cases h9 : i = 9
  · subst i
    exact chunk_1609
  omega

end BealMatveevBeal.BealMatveevBealV25B0Search.Chunked10e6
