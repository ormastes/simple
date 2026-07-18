#include <chrono>
#include <cstdlib>
#include <fstream>
#include <string>
#include <thread>
#include <vector>

#include "api/replay/renderdoc_replay.h"

static int env_int(const char *name, int fallback)
{
  const char *value = getenv(name);
  if(value == nullptr || value[0] == '\0')
    return fallback;
  char *end = nullptr;
  long parsed = strtol(value, &end, 10);
  return end != nullptr && *end == '\0' ? (int)parsed : fallback;
}

static std::string env_str(const char *name, const char *fallback)
{
  const char *value = getenv(name);
  return value != nullptr && value[0] != '\0' ? std::string(value) : std::string(fallback);
}

static void append_line(const std::string &path, const std::string &key, const std::string &value)
{
  std::ofstream out(path, std::ios::app);
  out << key << "=" << value << "\n";
}

static std::string message_type_name(TargetControlMessageType type)
{
  switch(type)
  {
    case TargetControlMessageType::Unknown: return "Unknown";
    case TargetControlMessageType::Disconnected: return "Disconnected";
    case TargetControlMessageType::Busy: return "Busy";
    case TargetControlMessageType::Noop: return "Noop";
    case TargetControlMessageType::NewCapture: return "NewCapture";
    case TargetControlMessageType::CaptureCopied: return "CaptureCopied";
    case TargetControlMessageType::NewChild: return "NewChild";
    case TargetControlMessageType::CaptureProgress: return "CaptureProgress";
    case TargetControlMessageType::RegisterAPI: return "RegisterAPI";
    case TargetControlMessageType::CapturableWindowCount: return "CapturableWindowCount";
    case TargetControlMessageType::RequestShow: return "RequestShow";
  }
  return "Other";
}

int main()
{
  std::string out_path = env_str("RDOC_TARGET_CONTROL_OUT", "build/renderdoc/target-control.env");
  uint32_t wanted_pid = (uint32_t)env_int("RDOC_TARGET_CONTROL_PID", 0);
  int timeout_s = env_int("RDOC_TARGET_CONTROL_TIMEOUT_SECS", 20);
  int wait_api_s = env_int("RDOC_TARGET_CONTROL_WAIT_API_SECS", 0);
  std::string capture_out = env_str("RDOC_TARGET_CONTROL_CAPTURE_OUT", "");
  std::string client_name = env_str("RDOC_TARGET_CONTROL_CLIENT", "simple-renderdoc-target-control-cpp");

  {
    std::ofstream out(out_path);
    out << "rdoc_target_control_status=running\n";
    out << "rdoc_target_control_wanted_pid=" << wanted_pid << "\n";
    out << "rdoc_target_control_timeout_secs=" << timeout_s << "\n";
    out << "rdoc_target_control_wait_api_secs=" << wait_api_s << "\n";
    out << "rdoc_target_control_client=cpp\n";
  }

  std::vector<uint32_t> idents;
  uint32_t next_ident = 0;
  for(size_t i = 0; i < 256; i++)
  {
    next_ident = RENDERDOC_EnumerateRemoteTargets(rdcstr(""), next_ident);
    if(next_ident == 0)
      break;
    idents.push_back(next_ident);
  }

  append_line(out_path, "rdoc_target_control_ident_count", std::to_string(idents.size()));
  std::string joined;
  for(size_t i = 0; i < idents.size(); i++)
  {
    if(i > 0)
      joined += "|";
    joined += std::to_string(idents[i]);
  }
  append_line(out_path, "rdoc_target_control_idents", joined);

  ITargetControl *chosen = nullptr;
  uint32_t chosen_ident = 0;
  for(uint32_t ident : idents)
  {
    ITargetControl *target =
        RENDERDOC_CreateTargetControl(rdcstr(""), ident, rdcstr(client_name.c_str()), true);
    if(target == nullptr)
    {
      append_line(out_path, "rdoc_target_control_ident_" + std::to_string(ident) + "_connect",
                  "fail");
      continue;
    }

    uint32_t pid = target->GetPID();
    append_line(out_path, "rdoc_target_control_ident_" + std::to_string(ident) + "_pid",
                std::to_string(pid));
    append_line(out_path, "rdoc_target_control_ident_" + std::to_string(ident) + "_api",
                target->GetAPI().c_str());
    append_line(out_path, "rdoc_target_control_ident_" + std::to_string(ident) + "_target",
                target->GetTarget().c_str());

    if(wanted_pid == 0 || pid == wanted_pid)
    {
      chosen = target;
      chosen_ident = ident;
      break;
    }
    target->Shutdown();
  }

  if(chosen == nullptr)
  {
    append_line(out_path, "rdoc_target_control_status", "fail");
    append_line(out_path, "rdoc_target_control_reason", "no-matching-target");
    return 1;
  }

  append_line(out_path, "rdoc_target_control_chosen_ident", std::to_string(chosen_ident));
  append_line(out_path, "rdoc_target_control_chosen_pid", std::to_string(chosen->GetPID()));
  append_line(out_path, "rdoc_target_control_chosen_api", chosen->GetAPI().c_str());
  append_line(out_path, "rdoc_target_control_chosen_target", chosen->GetTarget().c_str());

  uint32_t pretrigger_message_count = 0;
  uint32_t pretrigger_noop_count = 0;
  uint32_t api_message_count = 0;
  uint32_t window_message_count = 0;
  std::string last_api_name;
  bool last_api_presenting = false;
  bool last_api_supported = false;
  uint32_t last_window_count = 0;

  auto record_message = [&](const TargetControlMessage &msg, const char *phase) {
    if(msg.type == TargetControlMessageType::RegisterAPI)
    {
      api_message_count++;
      last_api_name = msg.apiUse.name.c_str();
      last_api_presenting = msg.apiUse.presenting;
      last_api_supported = msg.apiUse.supported;
      append_line(out_path, std::string("rdoc_target_control_") + phase + "_api_name",
                  last_api_name);
      append_line(out_path, std::string("rdoc_target_control_") + phase + "_api_presenting",
                  last_api_presenting ? "1" : "0");
      append_line(out_path, std::string("rdoc_target_control_") + phase + "_api_supported",
                  last_api_supported ? "1" : "0");
      if(!msg.apiUse.supportMessage.empty())
        append_line(out_path, std::string("rdoc_target_control_") + phase + "_api_support_message",
                    msg.apiUse.supportMessage.c_str());
    }
    else if(msg.type == TargetControlMessageType::CapturableWindowCount)
    {
      window_message_count++;
      last_window_count = msg.capturableWindowCount;
      append_line(out_path, std::string("rdoc_target_control_") + phase + "_window_count",
                  std::to_string(last_window_count));
    }
    else if(msg.type != TargetControlMessageType::Noop)
    {
      append_line(out_path, std::string("rdoc_target_control_") + phase + "_message",
                  message_type_name(msg.type));
    }
  };

  if(wait_api_s > 0)
  {
    auto wait_deadline = std::chrono::steady_clock::now() + std::chrono::seconds(wait_api_s);
    while(std::chrono::steady_clock::now() < wait_deadline)
    {
      TargetControlMessage msg = chosen->ReceiveMessage(nullptr);
      pretrigger_message_count++;
      if(msg.type == TargetControlMessageType::Noop)
      {
        pretrigger_noop_count++;
      }
      else
      {
        record_message(msg, "pretrigger");
      }
      if(msg.type == TargetControlMessageType::RegisterAPI && msg.apiUse.presenting &&
         msg.apiUse.supported)
      {
        break;
      }
    }
  }

  append_line(out_path, "rdoc_target_control_pretrigger_message_count",
              std::to_string(pretrigger_message_count));
  append_line(out_path, "rdoc_target_control_pretrigger_noop_count",
              std::to_string(pretrigger_noop_count));
  append_line(out_path, "rdoc_target_control_api_message_count", std::to_string(api_message_count));
  append_line(out_path, "rdoc_target_control_window_message_count",
              std::to_string(window_message_count));
  append_line(out_path, "rdoc_target_control_last_api_name", last_api_name);
  append_line(out_path, "rdoc_target_control_last_api_presenting",
              last_api_presenting ? "1" : "0");
  append_line(out_path, "rdoc_target_control_last_api_supported", last_api_supported ? "1" : "0");
  append_line(out_path, "rdoc_target_control_last_window_count",
              std::to_string(last_window_count));

  chosen->TriggerCapture(1);
  append_line(out_path, "rdoc_target_control_trigger", "sent");

  auto deadline = std::chrono::steady_clock::now() + std::chrono::seconds(timeout_s);
  uint32_t noop_count = 0;
  uint32_t message_count = 0;
  while(std::chrono::steady_clock::now() < deadline)
  {
    TargetControlMessage msg = chosen->ReceiveMessage(nullptr);
    message_count++;
    if(msg.type == TargetControlMessageType::Noop)
    {
      noop_count++;
    }
    else
    {
      record_message(msg, "posttrigger");
    }
    if(msg.type == TargetControlMessageType::NewCapture)
    {
      append_line(out_path, "rdoc_target_control_message_count", std::to_string(message_count));
      append_line(out_path, "rdoc_target_control_noop_count", std::to_string(noop_count));
      append_line(out_path, "rdoc_target_control_capture_path", msg.newCapture.path.c_str());
      append_line(out_path, "rdoc_target_control_capture_id",
                  std::to_string(msg.newCapture.captureId));
      append_line(out_path, "rdoc_target_control_capture_api", msg.newCapture.api.c_str());
      if(!capture_out.empty())
      {
        chosen->CopyCapture(msg.newCapture.captureId, rdcstr(capture_out.c_str()));
        append_line(out_path, "rdoc_target_control_copy_requested", capture_out);
      }
      chosen->Shutdown();
      append_line(out_path, "rdoc_target_control_status", "pass");
      append_line(out_path, "rdoc_target_control_reason", "pass");
      return 0;
    }
  }

  chosen->Shutdown();
  append_line(out_path, "rdoc_target_control_message_count", std::to_string(message_count));
  append_line(out_path, "rdoc_target_control_noop_count", std::to_string(noop_count));
  append_line(out_path, "rdoc_target_control_status", "fail");
  append_line(out_path, "rdoc_target_control_reason", "no-new-capture-message");
  return 1;
}
