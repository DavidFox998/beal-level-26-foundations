import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0720
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0721
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0722
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0723
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0724
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0725
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0726
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0727
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0728
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0729

namespace BealMatveevBeal.BealMatveevBealV25B0Search.Chunked10e6

set_option maxRecDepth 4096
set_option maxHeartbeats 0

/-- Ten separate kernel-checked 500-value intervals. -/
theorem group_072 (i : ℕ) (hi : i < 10) :
    checkRange (500 * (10 * 72 + i)) (500 * (10 * 72 + i + 1)) = true := by
  by_cases h0 : i = 0
  · subst i
    exact chunk_0720
  by_cases h1 : i = 1
  · subst i
    exact chunk_0721
  by_cases h2 : i = 2
  · subst i
    exact chunk_0722
  by_cases h3 : i = 3
  · subst i
    exact chunk_0723
  by_cases h4 : i = 4
  · subst i
    exact chunk_0724
  by_cases h5 : i = 5
  · subst i
    exact chunk_0725
  by_cases h6 : i = 6
  · subst i
    exact chunk_0726
  by_cases h7 : i = 7
  · subst i
    exact chunk_0727
  by_cases h8 : i = 8
  · subst i
    exact chunk_0728
  by_cases h9 : i = 9
  · subst i
    exact chunk_0729
  omega

end BealMatveevBeal.BealMatveevBealV25B0Search.Chunked10e6
