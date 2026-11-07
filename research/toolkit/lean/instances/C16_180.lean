import RowBase_16

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace Row16

open ACBounds ACClosed ACKeys ACPack ACSlot

/-- chunk 180 of the cap-16 certificate: slots 184320 .. 185343 -/
theorem chk_180 : chunkCheck 16 T stdSt 184320 1024 = true := by decide +kernel

end Row16
