import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0130
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0131
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0132
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0133
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0134
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0135
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0136
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0137
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0138
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0139

namespace BealMatveevBeal.BealMatveevBealV25B0Search.Chunked10e6

set_option maxRecDepth 4096
set_option maxHeartbeats 0

/-- Ten separate kernel-checked 500-value intervals. -/
theorem group_013 (i : ℕ) (hi : i < 10) :
    checkRange (500 * (10 * 13 + i)) (500 * (10 * 13 + i + 1)) = true := by
  by_cases h0 : i = 0
  · subst i
    exact chunk_0130
  by_cases h1 : i = 1
  · subst i
    exact chunk_0131
  by_cases h2 : i = 2
  · subst i
    exact chunk_0132
  by_cases h3 : i = 3
  · subst i
    exact chunk_0133
  by_cases h4 : i = 4
  · subst i
    exact chunk_0134
  by_cases h5 : i = 5
  · subst i
    exact chunk_0135
  by_cases h6 : i = 6
  · subst i
    exact chunk_0136
  by_cases h7 : i = 7
  · subst i
    exact chunk_0137
  by_cases h8 : i = 8
  · subst i
    exact chunk_0138
  by_cases h9 : i = 9
  · subst i
    exact chunk_0139
  omega

end BealMatveevBeal.BealMatveevBealV25B0Search.Chunked10e6
