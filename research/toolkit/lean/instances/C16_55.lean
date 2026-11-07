import RowBase_16

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace Row16

open ACBounds ACClosed ACKeys ACPack ACSlot

/-- chunk 55 of the cap-16 certificate: slots 56320 .. 57343 -/
theorem chk_55 : chunkCheck 16 T stdSt 56320 1024 = true := by decide +kernel

end Row16
