import RowBase_16

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace Row16

open ACBounds ACClosed ACKeys ACPack ACSlot

/-- chunk 86 of the cap-16 certificate: slots 88064 .. 89087 -/
theorem chk_86 : chunkCheck 16 T stdSt 88064 1024 = true := by decide +kernel

end Row16
