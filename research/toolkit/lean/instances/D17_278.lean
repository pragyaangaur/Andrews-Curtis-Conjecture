import RowBase

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace Row17

open ACBounds ACClosed ACKeys ACPack ACSlot

/-- chunk 278 of the cap-17 certificate: slots 142336 .. 142847 -/
theorem chk_278 : chunkCheck 17 T stdSt 142336 512 = true := by decide +kernel

end Row17
