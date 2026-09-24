import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0140
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0141
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0142
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0143
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0144
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0145
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0146
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0147
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0148
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0149

namespace BealMatveevBeal.BealMatveevBealV25B0Search.Chunked10e6

set_option maxRecDepth 4096
set_option maxHeartbeats 0

/-- Ten separate kernel-checked 500-value intervals. -/
theorem group_014 (i : ℕ) (hi : i < 10) :
    checkRange (500 * (10 * 14 + i)) (500 * (10 * 14 + i + 1)) = true := by
  by_cases h0 : i = 0
  · subst i
    exact chunk_0140
  by_cases h1 : i = 1
  · subst i
    exact chunk_0141
  by_cases h2 : i = 2
  · subst i
    exact chunk_0142
  by_cases h3 : i = 3
  · subst i
    exact chunk_0143
  by_cases h4 : i = 4
  · subst i
    exact chunk_0144
  by_cases h5 : i = 5
  · subst i
    exact chunk_0145
  by_cases h6 : i = 6
  · subst i
    exact chunk_0146
  by_cases h7 : i = 7
  · subst i
    exact chunk_0147
  by_cases h8 : i = 8
  · subst i
    exact chunk_0148
  by_cases h9 : i = 9
  · subst i
    exact chunk_0149
  omega

end BealMatveevBeal.BealMatveevBealV25B0Search.Chunked10e6
