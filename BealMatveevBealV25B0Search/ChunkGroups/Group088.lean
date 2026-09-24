import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0880
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0881
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0882
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0883
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0884
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0885
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0886
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0887
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0888
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0889

namespace BealMatveevBeal.BealMatveevBealV25B0Search.Chunked10e6

set_option maxRecDepth 4096
set_option maxHeartbeats 0

/-- Ten separate kernel-checked 500-value intervals. -/
theorem group_088 (i : ℕ) (hi : i < 10) :
    checkRange (500 * (10 * 88 + i)) (500 * (10 * 88 + i + 1)) = true := by
  by_cases h0 : i = 0
  · subst i
    exact chunk_0880
  by_cases h1 : i = 1
  · subst i
    exact chunk_0881
  by_cases h2 : i = 2
  · subst i
    exact chunk_0882
  by_cases h3 : i = 3
  · subst i
    exact chunk_0883
  by_cases h4 : i = 4
  · subst i
    exact chunk_0884
  by_cases h5 : i = 5
  · subst i
    exact chunk_0885
  by_cases h6 : i = 6
  · subst i
    exact chunk_0886
  by_cases h7 : i = 7
  · subst i
    exact chunk_0887
  by_cases h8 : i = 8
  · subst i
    exact chunk_0888
  by_cases h9 : i = 9
  · subst i
    exact chunk_0889
  omega

end BealMatveevBeal.BealMatveevBealV25B0Search.Chunked10e6
