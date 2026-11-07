import RowBase

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace Row17

open ACBounds ACClosed ACKeys ACPack ACSlot

/-- chunk 460 of the cap-17 certificate: slots 235520 .. 236031 -/
theorem chk_460 : chunkCheck 17 T stdSt 235520 512 = true := by decide +kernel

end Row17
