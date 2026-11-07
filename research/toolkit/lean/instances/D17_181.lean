import RowBase

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace Row17

open ACBounds ACClosed ACKeys ACPack ACSlot

/-- chunk 181 of the cap-17 certificate: slots 92672 .. 93183 -/
theorem chk_181 : chunkCheck 17 T stdSt 92672 512 = true := by decide +kernel

end Row17
