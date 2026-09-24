import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0950
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0951
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0952
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0953
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0954
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0955
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0956
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0957
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0958
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0959

namespace BealMatveevBeal.BealMatveevBealV25B0Search.Chunked10e6

set_option maxRecDepth 4096
set_option maxHeartbeats 0

/-- Ten separate kernel-checked 500-value intervals. -/
theorem group_095 (i : ℕ) (hi : i < 10) :
    checkRange (500 * (10 * 95 + i)) (500 * (10 * 95 + i + 1)) = true := by
  by_cases h0 : i = 0
  · subst i
    exact chunk_0950
  by_cases h1 : i = 1
  · subst i
    exact chunk_0951
  by_cases h2 : i = 2
  · subst i
    exact chunk_0952
  by_cases h3 : i = 3
  · subst i
    exact chunk_0953
  by_cases h4 : i = 4
  · subst i
    exact chunk_0954
  by_cases h5 : i = 5
  · subst i
    exact chunk_0955
  by_cases h6 : i = 6
  · subst i
    exact chunk_0956
  by_cases h7 : i = 7
  · subst i
    exact chunk_0957
  by_cases h8 : i = 8
  · subst i
    exact chunk_0958
  by_cases h9 : i = 9
  · subst i
    exact chunk_0959
  omega

end BealMatveevBeal.BealMatveevBealV25B0Search.Chunked10e6
