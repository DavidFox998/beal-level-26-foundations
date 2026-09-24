import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1580
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1581
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1582
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1583
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1584
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1585
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1586
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1587
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1588
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1589

namespace BealMatveevBeal.BealMatveevBealV25B0Search.Chunked10e6

set_option maxRecDepth 4096
set_option maxHeartbeats 0

/-- Ten separate kernel-checked 500-value intervals. -/
theorem group_158 (i : ℕ) (hi : i < 10) :
    checkRange (500 * (10 * 158 + i)) (500 * (10 * 158 + i + 1)) = true := by
  by_cases h0 : i = 0
  · subst i
    exact chunk_1580
  by_cases h1 : i = 1
  · subst i
    exact chunk_1581
  by_cases h2 : i = 2
  · subst i
    exact chunk_1582
  by_cases h3 : i = 3
  · subst i
    exact chunk_1583
  by_cases h4 : i = 4
  · subst i
    exact chunk_1584
  by_cases h5 : i = 5
  · subst i
    exact chunk_1585
  by_cases h6 : i = 6
  · subst i
    exact chunk_1586
  by_cases h7 : i = 7
  · subst i
    exact chunk_1587
  by_cases h8 : i = 8
  · subst i
    exact chunk_1588
  by_cases h9 : i = 9
  · subst i
    exact chunk_1589
  omega

end BealMatveevBeal.BealMatveevBealV25B0Search.Chunked10e6
