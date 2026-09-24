import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0970
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0971
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0972
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0973
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0974
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0975
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0976
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0977
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0978
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0979

namespace BealMatveevBeal.BealMatveevBealV25B0Search.Chunked10e6

set_option maxRecDepth 4096
set_option maxHeartbeats 0

/-- Ten separate kernel-checked 500-value intervals. -/
theorem group_097 (i : ℕ) (hi : i < 10) :
    checkRange (500 * (10 * 97 + i)) (500 * (10 * 97 + i + 1)) = true := by
  by_cases h0 : i = 0
  · subst i
    exact chunk_0970
  by_cases h1 : i = 1
  · subst i
    exact chunk_0971
  by_cases h2 : i = 2
  · subst i
    exact chunk_0972
  by_cases h3 : i = 3
  · subst i
    exact chunk_0973
  by_cases h4 : i = 4
  · subst i
    exact chunk_0974
  by_cases h5 : i = 5
  · subst i
    exact chunk_0975
  by_cases h6 : i = 6
  · subst i
    exact chunk_0976
  by_cases h7 : i = 7
  · subst i
    exact chunk_0977
  by_cases h8 : i = 8
  · subst i
    exact chunk_0978
  by_cases h9 : i = 9
  · subst i
    exact chunk_0979
  omega

end BealMatveevBeal.BealMatveevBealV25B0Search.Chunked10e6
