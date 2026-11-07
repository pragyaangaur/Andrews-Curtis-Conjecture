import RowBase

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace Row17

open ACBounds ACClosed ACKeys ACPack ACSlot

/-- chunk 317 of the cap-17 certificate: slots 162304 .. 162815 -/
theorem chk_317 : chunkCheck 17 T stdSt 162304 512 = true := by decide +kernel

end Row17
