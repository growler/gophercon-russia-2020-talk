local output_dir = "."
local printresult

local ImageBitmap = {}
ImageBitmap.__index = ImageBitmap

local ImageVector = {}
ImageVector.__index = ImageVector

local images_table = {}

for _, v in ipairs(arg) do
   local t = string.match(v,"%-output%-directory=(.+)")
   if t then
      output_dir = t
      break
   end
end

local debug = function(...)
   io.stderr:write("\n")
   io.stderr:write(...)
   io.stderr:write("\n")
end

local image_types = {
   lossy = {
      ext = "jpg",
      kind = ImageBitmap,
      exts = {
         "jpeg", "jpg", "jp2", "j2k"
      }
   },
   lossless = {
      ext = "png",
      kind = ImageBitmap,
      exts = {
         "png", "gif", "pbm", "ppm"
      }
   },
   vector = {
      ext = "pdf",
      kind = ImageVector,
      exts = {
         "pdf", "eps", "svg"
      },
   }
}

local image_exts = {}

for _, o in pairs(image_types) do
   for _, v in ipairs(o.exts) do
      image_exts[v] = o
   end
end

-- docwidth == 0 && docheight == 0 -> nil
-- docwidth ~= 0 && docheight ~= 0 && keepaspectratio == 1 -> w x h
-- docwidth ~= 0 && docheight ~= 0 && keepaspectratio == 0 -> w x h !
-- docwidth ~= 0 && docheight == 0 -> w
-- docwidth == 0 && docheight ~= 0 -> x h
function geometry(width, height, docwidth, docheight, keepaspectratio)
   debug('width = '..width..', docwidth = '..docwidth)
   debug('height = '..height..', docheight = '..docheight)
   if docwidth == 0 then
      if docheight == 0 then
         debug('docheight is zero')
         return nil
      else -- docheight ~= 0
         if docheight < height then
            return "x"..docheight
         else
            return nil
         end
      end
   else -- docwidth ~= 0
      if docheight == 0 then
         if docwidth < width then
            return docwidth
         else
            return nil
         end
      else -- docheight ~= 0
         if docwidth < width and docheight < height then
            return nil
         else
            if keepaspectratio == 1 then
               return docwidth..'x'..docheight
            else
               return docwidth..'x'..docheight..'!'
            end
         end
      end
   end
end

function runcmd(params)
   local cmd = table.concat(params, ' ')
   debug(cmd)
   local ret, err = os.spawn(params)
   if ret == nil or ret ~= 0 then
      if err ~= nil then
         debug('Error running command '..cmd..' ('..err..')')
      else
         debug('Error running command '..cmd)
      end
      return false
   end
   return true
end

function ImageBitmap.resize(self, target)
   local params = {
      'convert',
      self.source.name .. '[0]',
      '+profile', '!icc,*',
      '-units', 'PixelsPerInch',
      '-density', self.dpi
   }
   local geom = geometry(
      self.source.width,
      self.source.height,
      self.width,
      self.height,
      self.keepaspectratio
   )
   if geom ~= nil then
      table.insert(params, '-resize')
      table.insert(params, geom)
   end
   local format
   if self.source.colors == "Grayscale" then
      format = 'PNG8'
   elseif self.source.colors == "TrueColorAlpha" then
      if self.source.depth == 16 then
         format = 'PNG64'
      else
         format = 'PNG32'
      end
   else
      if self.source.depth == 16 then
         format = 'PNG48'
      else
         format = 'PNG24'
      end
   end
   table.insert(params, '-format')
   table.insert(params, format)
   table.insert(params, format..':'..target)
   debug("running " .. table.concat(params, ' '))
   return runcmd(params)
end

function encode_lossless(src, dest, dpi, color, depth)
   local params = {
      'convert',
      src .. '[0]',
      '+profile', '!icc,*',
      '-units', 'PixelsPerInch',
      '-density', dpi
   }
   local format
   if color == "Grayscale" then
      format = 'PNG8'
   elseif color == "TrueColorAlpha" then
      if depth == 16 then
         format = 'PNG64'
      else
         format = 'PNG32'
      end
   else
      if depth == 16 then
         format = 'PNG48'
      else
         format = 'PNG24'
      end
   end
   table.insert(params, '-format')
   table.insert(params, format)
   table.insert(params, format..':'..dest)
   return runcmd(params)
end

function encode_lossy(src, dest, dpi, quality)
   local params = {
      'convert',
      src .. '[0]',
      '+profile', '!icc,*',
      '-units', 'PixelsPerInch',
      '-density', dpi,
      '-format', 'JP2',
      '-define', 'jp2:quality='..quality,
      'jp2:' .. dest
   }
   return runcmd(params)
end

local image_comparators = {
   -- PET
   function(src, dst)
      local stream = io.popen('compare_pngs' .. ' "' .. src .. '" "' .. dst .. '"')
      if stream == nil then
         return nil
      end
      local out = stream:read('*l')
      stream:close()
      if string.match(out, '^%d+%.%d+$') or string.match(out, "^%d$") then
         return "PET", tonumber(out), 1.1, 0.05
      else
         error("Invalid output from PET comparator: " .. out)
         return nil
      end
   end,
   -- PSNR
   function(src_image, dest_image) -- PSNR
   end
}

function compare_images(src, dest)
   while #image_comparators > 0 do
      local name, metric, target, err = (image_comparators[1])(src, dest)
      if name == nil then
         table.remove(image_comparators, 1)
      else
         return name, metric, target, err
      end
   end
   error("No image comparator found")
end

function ImageBitmap.try_lossy(self, source_lossless, quality)
   local temp_dest_lossless = self.cache.basename .. '-' .. quality .. '.dst.png'
   local temp_dest_lossy    = self.cache.basename .. '-' .. quality .. '.' .. self.type.ext
   local cleanup = function()
      os.remove(temp_dest_lossless)
      os.remove(temp_dest_lossy)
   end
   debug(source_lossless .. '->' .. temp_dest_lossy)
   if not encode_lossy(source_lossless, temp_dest_lossy, self.dpi, quality) then
      cleanup()
      return nil
   end
   debug(temp_dest_lossy .. '->' .. temp_dest_lossless)
   if not encode_lossless(temp_dest_lossy, temp_dest_lossless, self.dpi, self.source.colors, self.source.depth) then
      cleanup()
      return nil
   end
   local name, metric, target, err = compare_images(source_lossless, temp_dest_lossless)
   if name == nil then
      cleanup()
      return nill
   end
   debug(self.name .. " quality " .. quality .. " " .. name .. " metric = " .. metric)
   os.remove(temp_dest_lossless)
   return temp_dest_lossy, metric, target, err
end

function sign(x)
   return x > 0 and 1 or x < 0 and -1 or 0
end

local min_metric_change = 0.01

function process_lossy(self)
   -- unpack image to png
   local tmp_source_lossless = self.cache.basename .. '.src.png'
   if not self:resize(tmp_source_lossless) then
      return false
   end
   local quality, step, last_metric, last_step, direction = 30, 5
   while true do
      debug("quality = " .. quality .. ", step = " .. step .. ", last_metric = " .. tostring(last_metric))
      local name, metric, target, err = self:try_lossy(
         tmp_source_lossless,
         quality
      )
      if name == nil then
         os.remove(tmp_source_lossless)
         return false
      end
      local distance, metric_change = target - metric
      if last_metric ~= nil then
         metric_change = metric - last_metric
         if direction == nil then
            direction = sign(metric_change)
         end
      end
      if math.abs(distance) < err or (metric_change ~= nil and math.abs(metric_change) < (err/10))  then
         local new_size = lfs.attributes(name, "size")
         debug("size = "..self.source.size..", new size = "..new_size)
         if new_size > self.source.size then
            os.remove(tmp_source_lossless)
            os.remove(name)
            os.remove(self.cache.name)
            os.spawn({'cp', self.source.name, self.cache.name})
            return true
         else
            os.remove(tmp_source_lossless)
            os.remove(self.cache.name)
            os.rename(name, self.cache.name)
            return true
         end
      else
         os.remove(name)
         if metric_change ~= nil then
            local rate = math.abs(metric_change) * 2 / math.abs(step) / 3
            if rate == 0 then
               step = sign(direction) * min_metric_change
            else
               step = math.floor( distance * direction / min_metric_change / rate) * min_metric_change
               if math.abs(step) < min_metric_change then
                  if step == 0 then
                     step = sign(direction) * min_metric_change
                  else
                     step = sign(step) * min_metric_change
                  end
               end
            end
            debug("metric = "..metric..", last metric = "..last_metric..", distance = "..distance..", direction = "..direction..", step = "..step..", rate = "..rate)
         end
         quality = quality + step
         last_metric = metric
         last_step = step
      end
   end
   return false
end
image_types.lossy["proc"] = process_lossy

function process_lossless(self)
   return self:resize(self.cache.name)
end

image_types.lossless["proc"] = process_lossless

function process_vector(self)
   debug("real name "..self.source.name.." ext "..self.source.ext)
   if self.source.ext == "eps" or self.source.ext == "pdf" then
      self.cache.name = self.source.name
   end
   return true
end
image_types.vector["proc"] = process_vector

function file_ext(filename)
   local d, f, e
   f, e = string.match(filename, '^([^/]+)%.([^%./]+)$')
   if f == nil then
      d, f, e = string.match(filename, '^(.+)/([^/]+)%.([^%./]+)$')
      if d == nil then
         return nil, filename, nil
      end
      return d, f, e
   else
      return nil, f, e
   end
end

function Image(filename, docwidth, docheight, keepaspectratio, dpi)
   local dirname, basename, ext = file_ext(filename)
   local typ = image_exts[ext]
   if typ == nil then
      return nil
   end
   local self = setmetatable({}, typ.kind)
   local real_name = kpse.find_file(filename)
   if real_name == nil then
      return nil
   end
   local source_ct = lfs.attributes(real_name, 'modification')
   if source_ct == nil then
      return nil
   end
   local cache_basename
   if dirname == nil then
      cache_basename = basename
   else
      cache_basename = string.gsub(dirname, "/", "-")
      cache_basename = cache_basename .. '-' .. basename
   end
   self.name            = filename
   self.type            = typ
   self.keepaspectratio = keepaspectratio
   self.width           = docwidth
   self.height          = docheight
   self.dpi             = dpi
   self.cache_basename = cache_basename
   self.source = {
      name  = real_name,
      mtime = source_ct,
      ext   = ext
   }
   return self
end

function ImageVector.update_cache(self)
   if self.source.ext == self.type.ext then
      self.cache = {
         name = self.source.name
      }
      return true
   end
   if self.cache == nil then
      self.cache = {
         name = output_dir .. '/' .. self.cache_basename .. '.' .. self.type.ext
      }
   end
   self.cache.mtime = lfs.attributes(self.cache.name, 'modification')
   if self.cache.mtime ~= nil and self.cache.mtime >= self.source.mtime then
      return true
   end
   if self.source.ext == "eps" then
      return runcmd({
            'epstopdf',
            self.source.name,
            self.cache.name
      })
   elseif self.source.ext == "svg" then
      return runcmd({
            'svg2pdf',
            self.source.name,
            self.cache.name
      })
   end
end

function ImageBitmap.update_cache(self)
   if self.cache == nil then
      self.cache = {
         basename = output_dir ..
            '/' .. self.cache_basename ..
            '-' .. math.round(self.width) ..
            '-' .. math.round(self.height) ..
            '-' .. math.round(self.dpi)
      }
      self.cache.name = self.cache.basename .. '.' .. self.type.ext
   end
   self.cache.mtime = lfs.attributes(self.cache.name, 'modification')
   if self.cache.mtime ~= nil and self.cache.mtime >= self.source.mtime then
      return true
   end
   if not self:update_meta() then
      return false
   end
   return self.type.proc(self)
end

local identify_cmd = 'identify -format "OK %w %h %m %[type] %z %f"'

function ImageBitmap.update_meta(self)
   local stream = io.popen(identify_cmd .. ' "' .. self.source.name .. '[0]" 2>&1')
   local out = stream:read('*a')
   stream:close()
   local width, height, format, colors, depth = string.match(out, '^OK (%d+) (%d+) (%w+) (%w+) (%d+) (.+)$')
   if width == nil then
      error('Error reading properties for image ' .. self.source.name .. ': ' .. out)
      return false
   end
   self.source.size   = lfs.attributes(self.source.name, 'size')
   self.source.width  = tonumber(width)
   self.source.height = tonumber(height)
   self.source.colors = colors
   self.source.depth  = tonumber(depth)
   self.source.format = format
   return true
end

function include_image(filename, docwidth, docheight, keepaspectratio, dpi)
   debug("include image called with "..filename.." "..docwidth.." "..docheight)
   local image = Image(filename, docwidth, docheight, keepaspectratio, dpi)
   if image ~= nil and image:update_cache() then
      tex.print(image.cache.name)
   else
      tex.print(filename)
   end
end

function include_xkcd(name, docwidth, docheight, dpi)
   local fname = kpse.lookup(name..".png", {sibdir = "xkcd"})
   include_image(fname, docwidth, docheight, true, dpi)
end

function new_include_image(params, fname)
   debug("!!!", params, " ", fname)
end

if tex.print == nil then
   include_image(arg[1], tonumber(arg[2]), tonumber(arg[3]), tonumber(arg[4]), arg[5])
end
