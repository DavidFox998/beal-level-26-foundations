import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0990
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0991
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0992
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0993
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0994
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0995
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0996
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0997
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0998
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0999

namespace BealMatveevBeal.BealMatveevBealV25B0Search.Chunked10e6

set_option maxRecDepth 4096
set_option maxHeartbeats 0

/-- Ten separate kernel-checked 500-value intervals. -/
theorem group_099 (i : ℕ) (hi : i < 10) :
    checkRange (500 * (10 * 99 + i)) (500 * (10 * 99 + i + 1)) = true := by
  by_cases h0 : i = 0
  · subst i
    exact chunk_0990
  by_cases h1 : i = 1
  · subst i
    exact chunk_0991
  by_cases h2 : i = 2
  · subst i
    exact chunk_0992
  by_cases h3 : i = 3
  · subst i
    exact chunk_0993
  by_cases h4 : i = 4
  · subst i
    exact chunk_0994
  by_cases h5 : i = 5
  · subst i
    exact chunk_0995
  by_cases h6 : i = 6
  · subst i
    exact chunk_0996
  by_cases h7 : i = 7
  · subst i
    exact chunk_0997
  by_cases h8 : i = 8
  · subst i
    exact chunk_0998
  by_cases h9 : i = 9
  · subst i
    exact chunk_0999
  omega

end BealMatveevBeal.BealMatveevBealV25B0Search.Chunked10e6
