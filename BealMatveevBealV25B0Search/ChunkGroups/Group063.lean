import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0630
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0631
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0632
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0633
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0634
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0635
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0636
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0637
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0638
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0639

namespace BealMatveevBeal.BealMatveevBealV25B0Search.Chunked10e6

set_option maxRecDepth 4096
set_option maxHeartbeats 0

/-- Ten separate kernel-checked 500-value intervals. -/
theorem group_063 (i : ℕ) (hi : i < 10) :
    checkRange (500 * (10 * 63 + i)) (500 * (10 * 63 + i + 1)) = true := by
  by_cases h0 : i = 0
  · subst i
    exact chunk_0630
  by_cases h1 : i = 1
  · subst i
    exact chunk_0631
  by_cases h2 : i = 2
  · subst i
    exact chunk_0632
  by_cases h3 : i = 3
  · subst i
    exact chunk_0633
  by_cases h4 : i = 4
  · subst i
    exact chunk_0634
  by_cases h5 : i = 5
  · subst i
    exact chunk_0635
  by_cases h6 : i = 6
  · subst i
    exact chunk_0636
  by_cases h7 : i = 7
  · subst i
    exact chunk_0637
  by_cases h8 : i = 8
  · subst i
    exact chunk_0638
  by_cases h9 : i = 9
  · subst i
    exact chunk_0639
  omega

end BealMatveevBeal.BealMatveevBealV25B0Search.Chunked10e6
