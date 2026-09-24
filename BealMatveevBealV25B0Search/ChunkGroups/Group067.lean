import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0670
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0671
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0672
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0673
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0674
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0675
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0676
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0677
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0678
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0679

namespace BealMatveevBeal.BealMatveevBealV25B0Search.Chunked10e6

set_option maxRecDepth 4096
set_option maxHeartbeats 0

/-- Ten separate kernel-checked 500-value intervals. -/
theorem group_067 (i : ℕ) (hi : i < 10) :
    checkRange (500 * (10 * 67 + i)) (500 * (10 * 67 + i + 1)) = true := by
  by_cases h0 : i = 0
  · subst i
    exact chunk_0670
  by_cases h1 : i = 1
  · subst i
    exact chunk_0671
  by_cases h2 : i = 2
  · subst i
    exact chunk_0672
  by_cases h3 : i = 3
  · subst i
    exact chunk_0673
  by_cases h4 : i = 4
  · subst i
    exact chunk_0674
  by_cases h5 : i = 5
  · subst i
    exact chunk_0675
  by_cases h6 : i = 6
  · subst i
    exact chunk_0676
  by_cases h7 : i = 7
  · subst i
    exact chunk_0677
  by_cases h8 : i = 8
  · subst i
    exact chunk_0678
  by_cases h9 : i = 9
  · subst i
    exact chunk_0679
  omega

end BealMatveevBeal.BealMatveevBealV25B0Search.Chunked10e6
