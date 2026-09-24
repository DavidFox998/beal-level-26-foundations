import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1990
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1991
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1992
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1993
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1994
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1995
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1996
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1997
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1998
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1999

namespace BealMatveevBeal.BealMatveevBealV25B0Search.Chunked10e6

set_option maxRecDepth 4096
set_option maxHeartbeats 0

/-- Ten separate kernel-checked 500-value intervals. -/
theorem group_199 (i : ℕ) (hi : i < 10) :
    checkRange (500 * (10 * 199 + i)) (500 * (10 * 199 + i + 1)) = true := by
  by_cases h0 : i = 0
  · subst i
    exact chunk_1990
  by_cases h1 : i = 1
  · subst i
    exact chunk_1991
  by_cases h2 : i = 2
  · subst i
    exact chunk_1992
  by_cases h3 : i = 3
  · subst i
    exact chunk_1993
  by_cases h4 : i = 4
  · subst i
    exact chunk_1994
  by_cases h5 : i = 5
  · subst i
    exact chunk_1995
  by_cases h6 : i = 6
  · subst i
    exact chunk_1996
  by_cases h7 : i = 7
  · subst i
    exact chunk_1997
  by_cases h8 : i = 8
  · subst i
    exact chunk_1998
  by_cases h9 : i = 9
  · subst i
    exact chunk_1999
  omega

end BealMatveevBeal.BealMatveevBealV25B0Search.Chunked10e6
