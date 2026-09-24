import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1970
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1971
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1972
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1973
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1974
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1975
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1976
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1977
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1978
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1979

namespace BealMatveevBeal.BealMatveevBealV25B0Search.Chunked10e6

set_option maxRecDepth 4096
set_option maxHeartbeats 0

/-- Ten separate kernel-checked 500-value intervals. -/
theorem group_197 (i : ℕ) (hi : i < 10) :
    checkRange (500 * (10 * 197 + i)) (500 * (10 * 197 + i + 1)) = true := by
  by_cases h0 : i = 0
  · subst i
    exact chunk_1970
  by_cases h1 : i = 1
  · subst i
    exact chunk_1971
  by_cases h2 : i = 2
  · subst i
    exact chunk_1972
  by_cases h3 : i = 3
  · subst i
    exact chunk_1973
  by_cases h4 : i = 4
  · subst i
    exact chunk_1974
  by_cases h5 : i = 5
  · subst i
    exact chunk_1975
  by_cases h6 : i = 6
  · subst i
    exact chunk_1976
  by_cases h7 : i = 7
  · subst i
    exact chunk_1977
  by_cases h8 : i = 8
  · subst i
    exact chunk_1978
  by_cases h9 : i = 9
  · subst i
    exact chunk_1979
  omega

end BealMatveevBeal.BealMatveevBealV25B0Search.Chunked10e6
