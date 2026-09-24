import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1950
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1951
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1952
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1953
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1954
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1955
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1956
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1957
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1958
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1959

namespace BealMatveevBeal.BealMatveevBealV25B0Search.Chunked10e6

set_option maxRecDepth 4096
set_option maxHeartbeats 0

/-- Ten separate kernel-checked 500-value intervals. -/
theorem group_195 (i : ℕ) (hi : i < 10) :
    checkRange (500 * (10 * 195 + i)) (500 * (10 * 195 + i + 1)) = true := by
  by_cases h0 : i = 0
  · subst i
    exact chunk_1950
  by_cases h1 : i = 1
  · subst i
    exact chunk_1951
  by_cases h2 : i = 2
  · subst i
    exact chunk_1952
  by_cases h3 : i = 3
  · subst i
    exact chunk_1953
  by_cases h4 : i = 4
  · subst i
    exact chunk_1954
  by_cases h5 : i = 5
  · subst i
    exact chunk_1955
  by_cases h6 : i = 6
  · subst i
    exact chunk_1956
  by_cases h7 : i = 7
  · subst i
    exact chunk_1957
  by_cases h8 : i = 8
  · subst i
    exact chunk_1958
  by_cases h9 : i = 9
  · subst i
    exact chunk_1959
  omega

end BealMatveevBeal.BealMatveevBealV25B0Search.Chunked10e6
